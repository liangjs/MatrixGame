#!/usr/bin/env python  
  
from distutils.core import setup, Extension

MOD = 'MatrixGame'
setup(name=MOD, ext_modules=[Extension(MOD, sources=['MatrixGame.cpp'])]) 
