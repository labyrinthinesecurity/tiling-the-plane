#!/usr/bin/python3

from common import *
BRsolutions={}
BLsolutions={}
TLsolutions={}
TRsolutions={}

def init():
  global BRsolutions
  for m0 in starlist:
    if m0 not in BRsolutions:
      BRsolutions[m0]={}
    for m1 in starlist:
      if m1 not in BRsolutions[m0]:
        BRsolutions[m0][m1]={}
      for m2 in starlist:
        if m2 not in BRsolutions[m0][m1]:
          BRsolutions[m0][m1][m2]=sorted(list(BR(m0,m1,m2)))
  with open("BRsolutions.json","w") as f:
    json.dump(BRsolutions,f,indent=2)
    f.close()

def loadSolutions():
  global BRsolutions,BLsolutions,TLsolutions,TRsolutions
  with open("BRsolutions.json","r") as f:
    BRsolutions=json.load(f)
    f.close()
  for m0 in starlist:
    if m0 not in BLsolutions:
      BLsolutions[m0]={}
    if m0 not in TLsolutions:
      TLsolutions[m0]={}
    if m0 not in TRsolutions:
      TRsolutions[m0]={}
    for m1 in starlist:
      if m1 not in BLsolutions[m0]:
        BLsolutions[m0][m1]={}
      if m1 not in TLsolutions[m0]:
        TLsolutions[m0][m1]={}
      if m1 not in TRsolutions[m0]:
        TRsolutions[m0][m1]={}
      for m2 in starlist:
        if m2 not in BLsolutions[m0][m1]:
          ztl=BRsolutions[s(m0)][s(m1)][s(m2)]
          BLsolutions[m0][m1][m2]=[]
          for az in ztl:
            BLsolutions[m0][m1][m2].append(sInv(az))
          BLsolutions[m0][m1][m2]=sorted(BLsolutions[m0][m1][m2])
        if m2 not in TLsolutions[m0][m1]:
          ztr=BRsolutions[s(s(m0))][s(s(m1))][s(s(m2))]
          TLsolutions[m0][m1][m2]=[]
          for az in ztr:
            TLsolutions[m0][m1][m2].append(sInv(sInv(az)))
          TLsolutions[m0][m1][m2]=sorted(TLsolutions[m0][m1][m2])
        if m2 not in TRsolutions[m0][m1]:
          ztr=BRsolutions[sInv(m0)][sInv(m1)][sInv(m2)]
          TRsolutions[m0][m1][m2]=[]
          for az in ztl:
            TRsolutions[m0][m1][m2].append(s(az))
          TRsolutions[m0][m1][m2]=sorted(TRsolutions[m0][m1][m2])

def montecarlo_rotor():
  cnt0=-1
  ouch=-1
  avoided=-1
  t0=int(time.time())
  while cnt0<=10000:
    m0=random.choice(starlist)
    m1=random.choice(starlist)
    m2=random.choice(starlist)
    m3=random.choice(starlist)
    m4=random.choice(starlist)
    m5=random.choice(starlist)
    m6=random.choice(starlist)
    m7=random.choice(starlist)
    iss=set(BRsolutions[m0][m1][m2])
    if len(iss)==0:
      avoided+=1
      continue
    zcss=BRsolutions[sInv(m3)][sInv(m4)][sInv(m1)]
    if len(zcss)==0:
      avoided+=1
      continue
    css=set()
    for zc in zcss:
      css.add(s(zc))
    zc2ss=BRsolutions[sInv(sInv(m5))][sInv(sInv(m6))][sInv(sInv(m4))]
    if len(zc2ss)==0:
      avoided+=1
      continue
    c2ss=set()
    for zc in zc2ss:
      c2ss.add(s(s(zc)))
    zc3ss=BRsolutions[s(m7)][s(m2)][s(m6)]
    if len(zc3ss)==0:
      avoided+=1
      continue
    c3ss=set()
    for zc in zc3ss:
      c3ss.add(sInv(zc))
    inter=iss & css & c2ss & c3ss
    if len(inter)==0:
      print(sorted(iss))
      print(sorted(css))
      print(sorted(c2ss))
      print(sorted(c3ss))
      print(" ")
      print(inter)
      ouch+=1
      print(cnt0,m0,m1,m2,m3,m4,m5,m6,m7,"ouch!")
#      tile_image(f"monte-{m0}{m1}{m2}{m3}{m4}{m5}{m6}{m7}",tiler(m0,m1,m2,m3,m4,m5,m6,m7))
#      sys.exit()
    else:
      print(cnt0,m0,m1,m2,m3,m4,m5,m6,m7)
    cnt0+=1
  print("attempts",cnt0,"issues",ouch)

def sequential_rotor():
  cnt=-1
  cnt0=-1
  ouch=0
  t0=int(time.time())
  for m0 in starlist:
    cnt0+=1
    cnt1=-1
    print("m0",cnt0)
    for m1 in starlist:
      cnt1+=1
      cnt2=-1
      print("  m1",cnt1,int(time.time())-t0)
      for m2 in starlist:
        cnt2+=1
        print("    m2",cnt2,int(time.time())-t0)
        print("initial condition",m0,m1,m2)
        iss=set(BRsolutions[m0][m1][m2])
        for m3 in starlist:
          for m4 in starlist:
            zcss=BRsolutions[sInv(m3)][sInv(m4)][sInv(m1)]
            css=set()
            for zc in zcss:
              css.add(s(zc))
            for m5 in starlist:
              for m6 in starlist:
                zc2ss=BRsolutions[sInv(sInv(m5))][sInv(sInv(m6))][sInv(sInv(m4))]
                c2ss=set()
                for zc in zc2ss:
                  c2ss.add(s(s(zc)))
                for m7 in starlist:
                  if cnt>1000000:  # stop after 1 million iterations...
                    print("attempts",cnt,"issues",ouch)
                    sys.exit()
                  cnt+=1
                  zc3ss=BRsolutions[s(m7)][s(m2)][s(m6)]
                  c3ss=set()
                  for zc in zc3ss:
                    c3ss.add(sInv(zc))
                  inter=iss & css & c2ss & c3ss
#                  print(m0,m1,m2,m3,m4,m5,m6,m7,len(inter))
                  if len(inter)==0:
                    print(sorted(iss))
                    print(sorted(css))
                    print(sorted(c2ss))
                    print(sorted(c3ss))
                    print(len(inter),m0,m1,m2,m3,m4,m5,m6,m7,"ouch!")
                    ouch+=1
#                    tile_image(f"ouch-{m0}{m1}{m2}{m3}{m4}{m5}{m6}{m7}",tiler(m0,m1,m2,m3,m4,m5,m6,m7))
#                    sys.exit()
  

#init()
#sys.exit()

loadSolutions()
#sequential_rotor()
montecarlo_rotor()
