#!/usr/bin/python
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
# gswitch.py - A python based identity switching utility.
# Copyright 2013-2014, High Energy Physics, Imperial College
#
""" gSwitch - A python based identity switching utility.
"""

GS_VERSION = "1.0.5a (development version)"

import os
import pwd
import sys
import time
import base64
import getopt
import pycurl
import random
import socket
import struct
import syslog
import StringIO
from subprocess import Popen, PIPE


# A list of the argus servers to authenticate with (will be used at random).
GS_ARGUS_SERVERS = [ "https://my_argus1.domain:8154/authz",
                     "https://my_argus2.domain:8154/authz" ]
# Number of times to retry each server in the list.
GS_DEF_NUM_RETRIES = 2
# The path to get CA certs from
GS_DEF_CAPATH = "/path/to/my/CA/certificates"
# The mktemp template to write the target user proxy
GS_DEF_PROXY = "/tmp/x509up_p%d.gswitch.XXXXXX" % os.getpid()
# The default resource (this is probably fairly fixed)
GS_DEF_RES = "http://authz-interop.org/xacml/resource/resource-type/wn"
# The default action (you probably don't need to change this either)
GS_DEF_ACTION = "http://glite.org/xacml/action/execute"
# Check we can run sudo before trying to do a real switch?
# This can be set to true in production to "ignore" users that try to run
# sudo when they aren't allowed to.
GS_DEF_CHECKSUDO = True
# Users to reject immediately, i.e. = [ "user_a", "user_b" ]
# Note that the blocking is only advisory... They could easily circumvent it.
# This is mainly for users who insist on running this script, but who aren't
# in the sudoers file.
GS_BLOCKED_USERS = [ ]
# Enable extra debugging messages to /var/log/messages
# These include the full command line, PID, user, CLIENT_CERT env var and
# exit code (i.e. enough to get a good idea whether a user is doing anything
# wrong).
GS_DEBUG_MSG = True


class GSConsts:
  """ A class containing gSwitch constants. """
  # Client errors like invalid parameters / env variables
  ERROR_CLIENT     = 201
  # Internal errors (are there any?)
  ERROR_INTERNAL   = 202
  # Authentication of target proxy failed.
  ERROR_AUTH       = 203
  # The child return code overlaps these codes
  ERROR_CHILD_OVER = 204
  # The payload failed to execute for some reason
  ERROR_PAYLOAD    = 205
  # Used for overlapping return code detection
  MIN_ERROR_NO     = 201
  MAX_ERROR_NO     = 205
  

class GSHessian:
  """ A class implementing the Hessian v1.0.2 encoding standard.
      This currently only implements about 75% of the spec, which is
      enough to be interoperable with ARGUS. """

  # Object we use to signal special conditions
  SKIP = object() # Signal this value should be skipped
  EOF = object()  # Signal we got to the end of the current object

  @staticmethod
  def decode(code):
    """ Decode a base64 Hessian object into a python object. """
    raw_buf = StringIO.StringIO(base64.b64decode(code))
    return GSHessian.decode_stream(raw_buf)

  @staticmethod
  def decode_stream(stream, internal = False):
    """ Decode a python stream containing a raw hessian string into a
        python object.
        The internal flag causes objects like type codes and list ends to
        be processed, this should normally only be set to true in recursive
        calls from decode_stream itself. """

    # Get the type code and "switch" on it 
    type_code = stream.read(1)
    if type_code == 't' and internal:
      string_len_bytes = stream.read(2)
      string_len = struct.unpack(">H", string_len_bytes)[0]
      stream.read(string_len) # Just dump the type name
      return GSHessian.SKIP
    elif type_code == 'l' and internal:
      # Get the list len, but ignore it...
      list_len_bytes = stream.read(4)
      _ = struct.unpack(">i", list_len_bytes)[0]
      return GSHessian.SKIP
    elif type_code == 'z' and internal:
      return GSHessian.EOF
    elif type_code == 'N':
      return None
    elif type_code == 'T':
      return True
    elif type_code == 'F':
      return False
    elif type_code == 'I':
      int_bytes = stream.read(4)
      return struct.unpack(">i", int_bytes)[0]
    elif type_code == 'L':
      long_bytes = stream.read(8)
      return struct.unpack(">q", long_bytes)[0]
    elif type_code == 'D':
      double_bytes = stream.read(8)
      return struct.unpack(">d", double_bytes)[0]
    elif type_code == 'S':
      string_len_bytes = stream.read(2)
      string_len = struct.unpack(">H", string_len_bytes)[0]
      return stream.read(string_len)
    elif type_code == 'M':
      if (stream.read(1) != 't'):
        raise Exception("Type code missing from Map type.")
      type_len_bytes = stream.read(2)
      type_len = struct.unpack(">H", type_len_bytes)[0]
      type_name = stream.read(type_len)
      my_map = { "type" : type_name }
      while True:
        key = GSHessian.decode_stream(stream, True)
        if key == GSHessian.EOF:
          break
        value = GSHessian.decode_stream(stream)
        my_map[key] = value
      return my_map
    elif type_code == 'V':
      my_list = []
      while True:
        value = GSHessian.decode_stream(stream, True)
        if (value == GSHessian.EOF):
          break
        elif (value == GSHessian.SKIP):
          continue
        my_list.append(value)
      return my_list
    raise Exception("Unrecognised type '%c' in input stream!" % type_code)

  @staticmethod
  def encode(obj):
    """ Encode a python object into a base64 Hessian string. """
    my_str = GSHessian.encode_stream(obj)
    return base64.encodestring(my_str)

  @staticmethod
  def encode_stream(obj):
    """ Encode a python object into a raw Hessian string. """
    # Switch based on the type of object to serialise
    if obj == None:
      return "N"
    elif type(obj) is bool:
      if (obj): return "T"
      return "F"
    elif type(obj) is int:
      # An int may be normal or long
      if (obj > 0xFFFFFFFF):
        int_str = 'L' + struct.pack(">q", obj)
      else:
        int_str = 'I' + struct.pack(">i", obj)
      return int_str
    elif type(obj) is float:
      return 'D' + struct.pack(">d", obj)
    elif type(obj) is str:
      return 'S' + struct.pack(">H", len(obj)) + obj
    elif type(obj) is dict:
      dict_str = "Mt"
      if "type" in obj:
        dict_str += struct.pack(">H", len(obj["type"])) + obj["type"]
      else:
        dict_str += struct.pack(">H", 0)
      for key in obj:
        if key == "type": continue
        dict_str += GSHessian.encode_stream(key)
        dict_str += GSHessian.encode_stream(obj[key])
      dict_str += "z"
      return dict_str
    elif type(obj) is list:
      list_str = 'V'
      for item in obj:
        list_str += GSHessian.encode_stream(item)
      list_str += "z"
      return list_str
    raise Exception("Unrecognised object '%s'!" % type(obj))


class GSObjects:
  """ A collection of functions which process the objects that Argus uses for
      its RPC calls. """

  @staticmethod
  def create_param(param_type, param_array):
    """ Create a param array object, the most common part of an Argus object.

        Param array should be a list of tuples, each tuple should look like:
        ( The id of the attribute, The value of the attribute,
          The dataType of the attribute or "None" if it shouldn't have one) """
    param_dict = { "type" : param_type }
    param_list = []
    for param in param_array:
      attr = { "type":   "org.glite.authz.common.model.Attribute",
               "id":     param[0],
               "values": [param[1]] }
      if (param[2]):
        attr["dataType"] = param[2]
      param_list.append(attr)
    param_dict["attributes"] = param_list
    return param_dict

  @staticmethod
  def create_request(cert, host, resid, actid):
    """ Create a full base64 Hessian encoded argus request object. """
    # Create each part of the request object we need separately
    action = GSObjects.create_param("org.glite.authz.common.model.Action",
               [("urn:oasis:names:tc:xacml:1.0:action:action-id",
                 actid,
                 None)
               ])
    env = GSObjects.create_param("org.glite.authz.common.model.Environment",
               [("http://authz-interop.org/xacml/subject/cert-chain",
                 cert,
                 None),
                ("http://glite.org/xacml/attribute/profile-id",
                 "http://glite.org/xacml/profile/grid-wn/1.0",
                 "http://www.w3.org/2001/XMLSchema#anyURI")
               ])
    subj = GSObjects.create_param("org.glite.authz.common.model.Subject",
               [("http://authz-interop.org/xacml/subject/cert-chain",
                 cert,
                 None),
                ("urn:oasis:names:tc:xacml:1.0:subject:key-info",
                 cert,
                 "http://www.w3.org/2001/XMLSchema#string")
               ])
    res = GSObjects.create_param("org.glite.authz.common.model.Resource",
               [("urn:oasis:names:tc:xacml:1.0:resource:resource-id",
                 resid,
                 None),
                ("http://authz-interop.org/xacml/resource/dns-host-name",
                 host,
                 None)
               ])
    # Merge the parts to create the final request
    req = { "type":        "org.glite.authz.common.model.Request",
            "action":      action,
            "environment": env,
            "subjects":    [ subj ],
            "resources":   [ res ]
          }
    return GSHessian.encode(req)

  @staticmethod
  def decode_reply(code):
    """ Decode a full base64 Hessian encoded argus reply object
        and extract just the username field of it (returning it as a str).
        Exceptions will be thrown if a proper error occurs,
        if the user is not authorised then None will be returned. """
    reply = GSHessian.decode(code)
    if reply["type"] != "org.glite.authz.common.model.Response":
      raise Exception("Unknown reply object type.")
    results = reply["results"]
    if len(results) != 1:
      raise Exception("Unexpected number of results found.")
    result = results[0]
    if result["type"] != "org.glite.authz.common.model.Result":
      raise Exception("Unexpected result object type.")
    # Now for the important check, argus "decision" field
    # The only permissible reply is "1"
    if result["decision"] != 1:
      return None
    obligs = result["obligations"]
    if len(obligs) != 1:
      raise Exception("Unexpected number of obligations.")
    oblig = obligs[0]
    if oblig["type"] != "org.glite.authz.common.model.Obligation":
      raise Exception("Unknown obligation type.")
    for attr in oblig["attributeAssignments"]:
      if attr["attributeId"] == "http://glite.org/xacml/attribute/user-id":
        return attr["value"]
    raise Exception("User ID not found in reply attributes.")


class GSUtil:
  """ A class with generally useful functions for gSwitch. """

  @staticmethod
  def load_proxy(proxy_file, public_only = True):
    """ Loads a PEM encoded proxy file, optionally extracting just the
        public parts and returns them as a string. """
    fd = os.open(proxy_file, os.O_RDONLY)
    file_in = os.fdopen(fd, 'r')
    full_proxy = file_in.read()
    file_in.close()
    if not public_only:
      return full_proxy
    # Now we have the full proxy, we get only the public key bits
    proxy_split = full_proxy.split('\n')
    add_line = False
    public_proxy = ""
    for proxy_line in proxy_split:
      if (proxy_line.find("BEGIN CERTIFICATE") != -1):
        add_line = True
      if add_line: public_proxy += proxy_line + "\n"
      if (proxy_line.find("END CERTIFICATE") != -1):
        add_line = False
    return public_proxy

  @staticmethod
  def check_cert(cert_file):
    """ Checks a certificate for internal consistency. Argus performs the
        further checks against the cert and VOMS signature.
        We do this by shelling openssl as some version of pyOpenSSL lack
        the functions for this. 
        Returns true if everything is OK. """
    test_data = "This is the string that is encrypted. %f" % random.random()
    enc_cmd = [ "/usr/bin/openssl", "rsautl", "-certin", "-inkey", cert_file,
                "-encrypt" ]
    dec_cmd = [ "/usr/bin/openssl", "rsautl", "-inkey", cert_file,
                "-decrypt" ]
    # Store & Clear the LD_LIBRARY_PATH if needed
    ld_path = None
    if 'LD_LIBRARY_PATH' in os.environ:
      ld_path = os.environ['LD_LIBRARY_PATH']
      del os.environ['LD_LIBRARY_PATH']
    # Encrypt the test string
    p = Popen(enc_cmd, stdin = PIPE, stdout = PIPE, stderr = PIPE)
    p.stdin.write(test_data)
    encoded_data, _ = p.communicate()
    # Decode the encrypted data
    p = Popen(dec_cmd, stdin = PIPE, stdout = PIPE, stderr = PIPE)
    p.stdin.write(encoded_data)
    output_data, _ = p.communicate()
    # Restore the LD_LIBRARY_PATH
    if ld_path:
      os.environ['LD_LIBRARY_PATH'] = ld_path
    # Now check the result
    return (output_data == test_data)

  @staticmethod
  def write_proxy(target_user, proxy_templ, proxy_data, debug = False):
    """ Write a temporary proxy file as another user using sudo. """
    cmd = [ '/usr/bin/sudo', '-n', '-u', target_user, '--',
            '/bin/sh', '-c' ]
    if "XXX" in proxy_templ:
      # Proxy file is a mktemp template
      cmd += [ 'ID=`/bin/mktemp %s` && /bin/cat >> "${ID}" ' \
               '&& /bin/echo "${ID}"' % proxy_templ
             ]
    else:
      # Template is actually a full path
      cmd += [ 'ID="%s" && /bin/cat >> "${ID}" ' \
               '&& /bin/echo "${ID}"' % proxy_templ
             ]
    if debug:
      sys.stderr.write("%s\n" % cmd)
      return "/tmp/fake.debug.proxy.name"
    p = Popen(cmd, stdin = PIPE, stdout = PIPE, stderr = PIPE)
    p.stdin.write(proxy_data)
    proxy_file, error_msg = p.communicate()
    proxy_file = proxy_file.strip()
    if p.returncode:
      error_msg = error_msg.strip()
      raise Exception("Failed to write payload proxy file as %s (%s)." % \
                       (target_user, error_msg))
    return proxy_file
    

  @staticmethod
  def check_sudo(target_user,
                 debug = False):
    """ Check if sudo access to this account is allowed.
        Returns true if it is. """
    cmd = [ "/usr/bin/sudo", '-n', '-u', '%s' % target_user, "-l",
            "--", "/bin/hostname" ]
    if debug:
      sys.stderr.write("%s\n" % cmd)
      return True
    p = Popen(cmd, stdout = PIPE, stdin = PIPE)
    _ = p.communicate()
    return (p.returncode == 0)

  @staticmethod
  def run_executable(target_user,
                     exec_args,
                     background = False,
                     debug = False):
    """ Run a command as another user using sudo. """
    cmd = [ '/usr/bin/sudo', '-n', '-u', '%s' % target_user ]
    if background:
      cmd += [ '-b' ]
    cmd += [ '--' ] + exec_args
    if debug:
      sys.stderr.write("%s\n" % cmd)
      return 0
    p = Popen(cmd)
    p.communicate()
    return p.returncode


class GSArgus:
  """ A set of functions for interacting with Argus servers. """

  @staticmethod
  def do_lookup(url,
                inner_proxy,
                usercert,
                userkey,
                capath):
    """ Post a single request to an argus server. """
    req = GSObjects.create_request(inner_proxy,
                                   os.uname()[1],
                                   GS_DEF_RES,
                                   GS_DEF_ACTION)
    curl = pycurl.Curl()
    curl.setopt(curl.URL, url)
    curl.setopt(curl.POSTFIELDS, req)
    curl.setopt(curl.CAPATH, capath)
    curl.setopt(curl.CAINFO, usercert)
    curl.setopt(curl.SSLCERT, usercert)
    curl.setopt(curl.SSLKEY, userkey)
    # We get the response through the returned body
    body = StringIO.StringIO()
    curl.setopt(curl.WRITEFUNCTION, body.write)
    # Here goes nothing!
    curl.perform()
    code = curl.getinfo(pycurl.HTTP_CODE)
    if code != 200:
      raise Exception("Argus request failed with code %d." % code)
    username = GSObjects.decode_reply(body.getvalue())
    return username

  @staticmethod
  def map(url_list,
          inner_proxy,
          usercert,
          userkey,
          capath,
          num_retries = GS_DEF_NUM_RETRIES):
    """ Attempt a request on a collection of Argus servers until
        one is successful or the retry count is reached. """
    last_error = ""
    # Make the choice of server deterministic for a given host
    random.seed(socket.gethostname())
    random.shuffle(url_list)
    for url in url_list:
      for _ in range(0, num_retries):
        try:
          username = GSArgus.do_lookup(url,
                                       inner_proxy,
                                       usercert,
                                       userkey,
                                       capath)
          return username # Success!
        except Exception, err:
          last_error = str(err)
          time.sleep(1) # Don't flood the server on error
    raise Exception("All attempts exhausted, last error: %s" % last_error)

def print_version():
  """ Print just the version information and exit. """
  print "gSwitch v" + GS_VERSION
  sys.exit(0)

def print_help():
  """ Print the program usage information and exit. """
  print "gSwitch -- An identity switching utility."
  print "Version: gSwitch v" + GS_VERSION
  print "Usage: gSwitch [options] <command> [args...]"
  print ""
  print "Option meanings:"
  print "  -h / --help       -- Show this text."
  print "  -v / --version    -- Show version information."
  print "  -V / --defines    -- Show config information."
  print "  -b / --background -- Run command in background."
  print "  -d / --debug      -- Only print what would be run."
  print ""
  sys.exit(0)

def print_defines():
  """ Print the program configuration and exit. """
  print 'Servers = %s' % GS_ARGUS_SERVERS
  print 'Default proxy location = %s' % GS_DEF_PROXY
  sys.exit(0)

if __name__ == '__main__':
  run_background = False
  debug = False

  if GS_DEBUG_MSG:
    syslog.syslog("gSwitch[%d]: %s %s\n" % (os.getpid(),
                                            pwd.getpwuid(os.geteuid())[0],
                                            sys.argv))

  try:
    optlist, args = getopt.getopt(sys.argv[1:], 'hvVbd',
                      ['help', 'version', 'defines', 'background', 'debug'])
  except getopt.GetoptError, err:
    sys.stderr.write("%s\n" % str(err))
    print_help()

  for opt in optlist:
    if opt[0] in ("-h", "--help"):
      print_help()
    if opt[0] in ("-v", "--version"):
      print_version()
    if opt[0] in ("-V", "--defines"):
      print_defines()
    if opt[0] in ("-b", "--background"):
      run_background = True
    if opt[0] in ("-d", "--debug"):
      debug = True

  # Catch any errors further down the stack
  try:
    if len(args) < 1:
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: No payload command.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0]))
      sys.stderr.write("You must specify a payload command to run.\n")
      sys.exit(GSConsts.ERROR_CLIENT)

    # Before doing anything further, check the blocked user list
    # Use PWD & geteuid as getlogin() fails in some instances
    if pwd.getpwuid(os.geteuid())[0] in GS_BLOCKED_USERS:
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: User blocked.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0]))
      sys.stderr.write("You are not allowed to run this executable.\n")
      sys.exit(GSConsts.ERROR_AUTH)

    ## First check that we have our required environment variables
    if not "X509_USER_PROXY" in os.environ:
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: X509_USER_PROXY unset.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0]))
      sys.stderr.write("X509_USER_PROXY must be set to the pilot proxy.\n")
      sys.exit(GSConsts.ERROR_CLIENT)
    if not "GLEXEC_CLIENT_CERT" in os.environ:
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: GLEXEC_CLIENT_CERT unset.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0]))
      sys.stderr.write("GLEXEC_CLIENT_CERT must be set to the " \
                       "target user proxy.\n")
      sys.exit(GSConsts.ERROR_CLIENT)
    pilot_proxy = os.path.abspath(os.environ["X509_USER_PROXY"])
    target_proxy = os.path.abspath(os.environ["GLEXEC_CLIENT_CERT"])

    if GS_DEBUG_MSG:
      syslog.syslog("gSwitch[%d]: %s Target proxy: %s\n" % \
                      (os.getpid(),
                       pwd.getpwuid(os.geteuid())[0],
                       target_proxy))
    # Optional environment variables
    if not 'GLEXEC_SOURCE_PROXY' in os.environ:
      job_src_proxy = target_proxy
    else:
      job_src_proxy = os.path.abspath(os.environ["GLEXEC_SOURCE_PROXY"])
    if not "GLEXEC_TARGET_PROXY" in os.environ:
      job_tgt_proxy = GS_DEF_PROXY
    else:
      job_tgt_proxy = os.environ["GLEXEC_TARGET_PROXY"]
  
    # Now check that we can access all of the files we're going to use
    if not os.access(pilot_proxy, os.R_OK):
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: %s.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0],
                         "X509_USER_PROXY unreadable"))
      sys.stderr.write("Cannot read X509_USER_PROXY '%s'.\n" % pilot_proxy)
      sys.exit(GSConsts.ERROR_CLIENT)
    if not os.access(target_proxy, os.R_OK):
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: %s.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0],
                         "GLEXEC_CLIENT_CERT unreadable"))
      sys.stderr.write("Cannot read GLEXEC_CLIENT_CERT '%s'.\n" % target_proxy)
      sys.exit(GSConsts.ERROR_CLIENT)
    if not os.access(job_src_proxy, os.R_OK):
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: %s.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0],
                         "GLEXEC_SOURCE_PROXY unreadable"))
      sys.stderr.write("Cannot read GLEXEC_SOURCE_PROXY '%s'.\n" \
                         % job_src_proxy)
      sys.exit(GSConsts.ERROR_CLIENT)

    # First we check the client proxy we have seems ok
    if not GSUtil.check_cert(target_proxy):
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: Consistency check failed.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0]))
      sys.stderr.write("Target proxy failed the consistency check.\n")
      sys.exit(GSConsts.ERROR_AUTH)

    # Now we have the parameters, we can start by mapping the user
    # target_name gets set to the username the payload should run as
    target_proxy_str = GSUtil.load_proxy(target_proxy)
    target_name = GSArgus.map(GS_ARGUS_SERVERS,
                              target_proxy_str,
                              pilot_proxy,
                              pilot_proxy,
                              GS_DEF_CAPATH)
    if not target_name:
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: Authentication failed.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0]))
      sys.stderr.write("Authentication failed.\n")
      sys.exit(GSConsts.ERROR_AUTH)

    # Check that we can actually successfully sudo,
    # if not, exit so we don't generate e-mail if that option is enabled
    if GS_DEF_CHECKSUDO and (not GSUtil.check_sudo(target_name, debug)):
      if GS_DEBUG_MSG:
        syslog.syslog("gSwitch[%d]: %s ERROR: User not authorised.\n" % \
                        (os.getpid(),
                         pwd.getpwuid(os.geteuid())[0]))
      sys.stderr.write("Current user not authorised to switch account.\n")
      sys.exit(GSConsts.ERROR_AUTH)

    # We now have a user name, so we can attempt to copy the proxy
    job_proxy_data = GSUtil.load_proxy(job_src_proxy, False)
    new_proxy_name = GSUtil.write_proxy(target_name,
                                        job_tgt_proxy,
                                        job_proxy_data,
                                        debug)

    # We change the environemnt now to set X509_USER_PROXY to the new cert
    # This will be inherited by the payload
    os.environ["X509_USER_PROXY"] = new_proxy_name

    # Run the real payload
    retval = GSUtil.run_executable(target_name, args, run_background, debug)

    # Attempt to delete the payload proxy
    if not run_background:
      GSUtil.run_executable(target_name,
                            [ '/bin/rm', '-f', new_proxy_name ],
                            False,
                            debug)

    # Finally exit with the error code
    if GS_DEBUG_MSG:
      syslog.syslog("gSwitch[%d]: %s Exit (Child Code: %d).\n" % \
                      (os.getpid(),
                       pwd.getpwuid(os.geteuid())[0],
                       retval))
    if (retval >= GSConsts.MIN_ERROR_NO) and \
         (retval <= GSConsts.MAX_ERROR_NO):
      sys.exit(GSConsts.ERROR_CHILD_OVER)
    else:
      sys.exit(retval)

  except SystemExit:
    # Exit silently on sys.exit()
    raise
  except Exception, err:
    if GS_DEBUG_MSG:
      syslog.syslog("gSwitch[%d]: %s Internal error: %s.\n" % \
                      (os.getpid(),
                       pwd.getpwuid(os.geteuid())[0],
                       str(err)))
    sys.stderr.write("gSwitch error: %s\n" % str(err))
    # Manually print the traceback and exit to avoid triggering abrt
    sys.stderr.write("%s\n" % (sys.exc_info()[2]))
    sys.exit(GSConsts.ERROR_CLIENT)

