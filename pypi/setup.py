#****************************************************************************
#* setup.py for PyBoolector
#****************************************************************************
import os
import sys
from setuptools import setup
from distutils.extension import Extension

if "PACKAGE_BUILD" in os.environ.keys() and os.environ["PACKAGE_BUILD"] != "":
    print("*******************************************************************")
    print("* WARNING: Building the PyBoolector Python extension from source   ")
    print("* WARNING: In general, this should not happen on Linux or macOS ")
    print("* WARNING: Windows is not supported, and will result in a fatal error")
    print("* ")
    print("*******************************************************************")

basedir = os.path.dirname(os.path.abspath(__file__))

version="3.2.3"
if os.path.isfile(os.path.join(basedir, "version.txt")):
    with open(os.path.join(basedir, "version.txt")) as fp:
        version = fp.read()
        version = version.strip()

if "BUILD_NUM" in os.environ.keys():
    version += ".%s" % os.environ["BUILD_NUM"]

# Static builds on macOS require specifying all archives
# Dynamic builds on other platforms don't
if sys.platform == "darwin":
    libraries=['boolector', 'btor2parser', 'cadical', 'lgl']
else:
    libraries=['boolector']

ext = Extension("pyboolector",
            sources=[
                'src/pyboolector.pyx',
                'src/pyboolector_abort.cpp',
                'src/boolector_py.c',
            ],
            language="c++",
            include_dirs=[
                '/usr/include/boolector',
                os.path.join(basedir, 'src')
            ],
            libraries=libraries
        )
ext.cython_directives={'language_level' : '3'}

CLASSIFIERS = [
    "Development Status :: 5 - Production/Stable",
    "Intended Audience :: Developers",
    "License :: OSI Approved :: MIT License",
    "Operating System :: OS Independent",
    "Programming Language :: Python",
    "Programming Language :: Python :: 3",
    "Programming Language :: Python :: 3.7",
    "Programming Language :: Python :: 3.8",
    "Programming Language :: Python :: 3.9",
    "Programming Language :: Python :: 3.10",
    "Programming Language :: Python :: 3.11",
    "Programming Language :: Python :: 3.12",
    "Programming Language :: Python :: Implementation :: CPython",
    "Topic :: Software Development :: Libraries :: Python Modules",
]

setup(
  name='PyBoolector',
  version=version,
  maintainer = "Matthew Ballance",
  maintainer_email = "matt.ballance@gmail.com",
  description = ("Python wrapper around the Boolector SMT solver"),
  long_description="""
    This package, specifically, enables the Boolector Python wrapper
    to be installed from PyPi
  """,
  licenses = ["MIT License"],
  download_url="https://pypi.org/project/PyBoolector/",
  url="https://github.com/boolector/boolector",
  setup_requires=[
    'setuptools_scm',
    'cython'
  ],
  ext_modules=[ ext ],
  classifiers=CLASSIFIERS
)


