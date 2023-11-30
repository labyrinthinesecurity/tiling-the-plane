#!/usr/bin/python3

from common import *

BRsolutions={}

def loadBRsolutions():
  global BRsolutions
  with open("BRsolutions.json","r") as f:
    BRsolutions=json.load(f)
    f.close()

loadBRsolutions()

for m0 in starlist:
  for m1 in starlist:
    for m2 in starlist:
      print(len(BRsolutions[m0][m1][m2]),m0,m1,m2)
