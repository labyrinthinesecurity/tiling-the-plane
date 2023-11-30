#!/usr/bin/python3
import sys,json,random
from z3 import *
from PIL import Image
import time

metalist= [ 'B', 'J', 'V', 'S', 'T', 'E', 'A', 'U', 'L', 'C', 'O', 'K', 'N', 'I', 'W', 'Y' ]
starlist= [ 'B', 'J', 'V', 'S', 'T', 'E', 'U', 'L', 'C', 'O', 'K', 'N', 'I', 'W', 'Y' ]

supertile=[[Bool(f"b_{i}_{j}") for j in range(4)] for i in range(4)]

metadict= {}
metadict['B']=0
metadict['J']=1
metadict['V']=2
metadict['S']=3

metadict['T']=4
metadict['E']=5
metadict['A']=6
metadict['U']=7


metadict['L']=8
metadict['C']=9
metadict['O']=10
metadict['K']=11

metadict['N']=12
metadict['I']=13
metadict['W']=14
metadict['Y']=15

Nb0=Bool('Nb0')
Nb1=Bool('Nb1')
Nb2=Bool('Nb2')
Nb3=Bool('Nb3')

Sb0=Bool('Sb0')
Sb1=Bool('Sb1')
Sb2=Bool('Sb2')
Sb3=Bool('Sb3')

Eb0=Bool('Eb0')
Eb1=Bool('Eb1')
Eb2=Bool('Eb2')
Eb3=Bool('Eb3')

Wb0=Bool('Wb0')
Wb1=Bool('Wb1')
Wb2=Bool('Wb2')
Wb3=Bool('Wb3')

def s(m):
  if m=='B':
    return 'Y'
  elif m=='Y':
    return 'B'
  elif m=='A':
    return 'A'
  elif m=='C':
    return 'C'
  elif m=='I':
    return 'J'
  elif m=='J':
    return 'K'
  elif m=='K':
    return 'L'
  elif m=='L':
    return 'I'
  elif m=='N':
    return 'E'
  elif m=='E':
    return 'S'
  elif m=='S':
    return 'O'
  elif m=='O':
    return 'N'
  elif m=='T':
    return 'U'
  elif m=='U':
    return 'V'
  elif m=='V':
    return 'W'
  elif m=='W':
    return 'T'
  return None

def sInv(m):
  if m=='B':
    return 'Y'
  elif m=='Y':
    return 'B'
  elif m=='A':
    return 'A'
  elif m=='C':
    return 'C'
  elif m=='I':
    return 'L'
  elif m=='J':
    return 'I'
  elif m=='K':
    return 'J'
  elif m=='L':
    return 'K'
  elif m=='N':
    return 'O'
  elif m=='O':
    return 'S'
  elif m=='S':
    return 'E'
  elif m=='E':
    return 'N'
  elif m=='T':
    return 'W'
  elif m=='U':
    return 'T'
  elif m=='V':
    return 'U'
  elif m=='W':
    return 'V'
  return None

def H(m):
  if m not in starlist:
    return None
  mi=metadict[m]
  mb=format(mi,'04b')
  if mb[2]=='0' and mb[3]=='1': # m0=0 or m1=1 except A
    return [ 'B', 'V', 'S', 'T', 'U', 'L', 'O', 'K', 'N', 'W', 'Y' ]
  else:
    return starlist

def Hinv(m):
  return H(s(s(m)))

def V(m):
  return H(sInv(m))

def Vinv(m):
  return H(s(m))

def BR(m0,m1,m2):
  slist=set([])
  m00=True
  m10=True
  m01=True
  m11=True
  mH00=True
  mH10=True
  mH01=True
  mH11=True
  mV00=True
  mV10=True
  mV01=True
  mV11=True
  if m0:
    mi=metadict[m0]
    mb=format(mi,'04b')
    if mb[0]=='0':
      m00=False
    m10=True
    if mb[2]=='0':
      m10=False
    m01=True
    if mb[1]=='0':
      m01=False
    if mb[3]=='0':
      m11=False
  if m1:
    mHi=metadict[m1]
    mHb=format(mHi,'04b')
    if mHb[0]=='0':
      mH00=False
    if mHb[2]=='0':
      mH10=False
    if mHb[1]=='0':
      mH01=False
    if mHb[3]=='0':
      mH11=False
  if m2:
    mVi=metadict[m2]
    mVb=format(mVi,'04b')
    if mVb[0]=='0':
      mV00=False
    if mVb[2]=='0':
      mV10=False
    if mVb[1]=='0':
      mV01=False
    if mVb[3]=='0':
      mV11=False
  zsol=Solver()
  conf=True
  core=True
  conf=And(conf,supertile[0][0]==m00,supertile[1][0]==m10,supertile[0][1]==m01,supertile[1][1]==m11)
  conf=And(conf,supertile[0][2]==mV00,supertile[1][2]==mV10,supertile[0][3]==mV01,supertile[1][3]==mV11)
  conf=And(conf,supertile[2][0]==mH00,supertile[3][0]==mH10,supertile[2][1]==mH01,supertile[3][1]==mH11)
  core=And(core,supertile[1][1]==False,supertile[2][1]==True,supertile[1][2]==True)
  zsol.add(conf)
  cnt=0
  while zsol.check()==sat:
    cnt+=1
    if cnt==1:
      zsol.push()
      zsol.add(core)
      if zsol.check()==unsat:
        return set(starlist) & set(H(m2)) & set (V(m1))
      zsol.pop()
      zsol.add(supertile[2][2]==True)
      continue
    localsupertile=[[False for _ in range(4)] for _ in range(4)]
    expr='zsol.add(Not(And('
    care={}
    for m in zsol.model():
      x=str(m)[2]
      y=str(m)[4]
      z=True
      if str(zsol.model()[m])=='False':
        z=False
      localsupertile[int(x)][int(y)]=z
      expr+='supertile['+x+']['+y+']=='+str(zsol.model()[m])+","
      if x not in care:
        care[x]={}
      if y not in care[x]:
        care[x][y]=0
    xlist=['2','3']
    ylist=['2','3']
    xexclude='2'
    yexclude='2'
    for x in xlist:
      if x not in care:
        for y in ylist:
          if y not in care[x]:
            if x==xexclude and y==yexclude:
              pass
            else:
              expr+='supertile['+x+']['+y+']==False,'
      else:
        for y in ylist:
          if y not in care[x]:
            if x==xexclude and y==yexclude:
              pass
            else:
              expr+='supertile['+x+']['+y+']==False,'


    expr=expr[:-1]+')))'
    if localsupertile[3][3]:
      mSb=1
    else:
      mSb=0
    if localsupertile[3][2]:
      mSb+=2
    if localsupertile[2][3]:
      mSb+=4
    if localsupertile[2][2]:
      mSb+=8
    mSi=metalist[mSb]
    slist.add(mSi)
    eval(expr)
  return slist & set(H(m2)) & set (V(m1))

def equality_check():
  for m in starlist:
    print(m)
    print(sorted(V(m)))
    print(sorted(H(sInv(m))))

    print(sorted(Vinv(m)))
    print(sorted(V(s(s(m)))))
    print(sorted(H(s(m))))

    print(sorted(Hinv(m)))
    print(sorted(H(s(s(m)))))

def tile_image(output_path, tile):
    # Open the input image
    try:
        zt = Image.open("zt.png")
    except IOError as e:
        print(f"Error opening image")
        sys.exit(1)
    try:
        zi = Image.open("zi.png")
    except IOError as e:
        print(f"Error opening image")
        sys.exit(1)


    # Get the size and mode of the input image
    zt_width, zt_height = zt.size
    zt_mode = zt.mode
    zi_width, zi_height = zi.size
    zi_mode = zi.mode

    tile_x=None
    tile_y=None

    for y in tile:
      if tile_y is None:
        tile_x=len(tile[y])
#      print(y,tile[y],len(tile[y]))
      tile_y=int(y)
    tile_y+=1
    # Create a new image with the desired tiling
    new_width = zt_width * tile_x * 2
    new_height = zt_height * tile_y * 2
    new_img = Image.new(zt_mode, (new_width, new_height))

    ly=-2
    for y in tile:
      ly+=2
      lx=-2
      for x in tile[y]:
        if x=='1' and y=='1':
          print(y,x,tile[y][x])
          lx+=2
          continue
        lx+=2
        mi=metadict[tile[y][x]]
        mb=format(mi,'04b')
        print(y,x,tile[y][x],mi,mb)
        if mb[0]=='0':
          new_img.paste(zi, (lx * zi_width, ly * zi_height))
        else:
          new_img.paste(zt, (lx * zi_width, ly * zi_height))
        if mb[2]=='0':
          new_img.paste(zi, ((lx+1) * zi_width, ly * zi_height))
        else:
          new_img.paste(zt, ((lx+1) * zi_width, ly * zi_height))
        if mb[3]=='0':
          new_img.paste(zi, ((lx+1) * zi_width, (ly+1) * zi_height))
        else:
          new_img.paste(zt, ((lx+1) * zi_width, (ly+1) * zi_height))
        if mb[1]=='0':
          new_img.paste(zi, (lx * zi_width, (ly+1) * zi_height))
        else:
          new_img.paste(zt, (lx * zi_width, (ly+1) * zi_height))
    try:
      new_img.save(output_path+".png", "PNG")
      print(f"Image tiled and saved as {output_path}")
    except IOError as e:
      print(f"Error saving the image: {e}")
      sys.exit(1)

def tiler(m0,m1,m2,m3,m4,m5,m6,m7):
  tile={}
  tile['0']={}
  tile['1']={}
  tile['2']={}
  tile['0']['0']=m0
  tile['0']['1']=m1
  tile['0']['2']=m3
  tile['1']['0']=m2
  tile['1']['1']='X'
  tile['1']['2']=m4
  tile['2']['0']=m7
  tile['2']['1']=m6
  tile['2']['2']=m5
  return tile

def rotor(m0,m1,m2,m3,m4,m5,m6,m7):
  iss=set(BRsolutions[m0][m1][m2])
  zcss=BRsolutions[sInv(m3)][sInv(m4)][sInv(m1)]
  css=set()
  for zc in zcss:
    css.add(s(zc))
  zc2ss=BRsolutions[sInv(sInv(m5))][sInv(sInv(m6))][sInv(sInv(m4))]
  c2ss=set()
  for zc in zc2ss:
    c2ss.add(s(s(zc)))
  zc3ss=BRsolutions[s(m7)][s(m2)][s(m6)]
  c3ss=set()
  for zc in zc3ss:
    c3ss.add(sInv(zc))
  inter=iss & css & c2ss & c3ss
  print(sorted(iss))
  print(sorted(css))
  print(sorted(c2ss))
  print(sorted(c3ss))
  print(" ")
  print(sorted(inter))
  print(len(inter),m0,m1,m2,m3,m4,m5,m6,m7,"ouch!")

def sequential_rotor():
  cnt=-1
  cnt0=-1
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
                  if cnt>1000000:
                    print(cnt)
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
#                    tile_image(f"ouch-{m0}{m1}{m2}{m3}{m4}{m5}{m6}{m7}",tiler(m0,m1,m2,m3,m4,m5,m6,m7))
#                    sys.exit()
