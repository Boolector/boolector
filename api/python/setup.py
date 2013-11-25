import os

from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext

ext_modules=[
    Extension("boolector",
              sources = ["boolector.pyx"],
              include_dirs = [os.getcwd() + "/../.."],
#              library_dirs = [os.getcwd() + "/../..", os.getcwd() + "/../../../lingeling"],
#              libraries = ['boolector', 'lgl']
              extra_objects = ["../../libboolector.a", "../../../lingeling/liblgl.a"]
    )
]

setup(
    cmdclass = {'build_ext': build_ext},
    ext_modules = ext_modules,
)
