###################### main function
NKKdegenerateinequality:=function(n,k)
local vars,ocanonical,o,canonical,r2,r1,LAb;
vars:=NKKVars(n,k);
ocanonical:=NKKOrbit(n,k);
o:=ocanonical[1];
canonical:=ocanonical[2];
r2:=nonc2canonical(o,n,k);
r1:=NKKcanonical2gr(canonical,r2,n,k);
list:=NKKinequality_no_degerate(r1,r2,n,k);
LAb:=LinrowsandAb(list);
# LAb[1] is the indices of equivalent constraints
# LAb[2] is the A matrix
# LAb[3] is the b vector
return LAb;
end;

######################

# all variables for (4,3,3)

NKKVars:= function(n,k)
  local i,vlist, t, tp;
  vlist := [];
  for i in [1..n] do
    Append(vlist,[[i]]);
  od;
  t := Tuples([1..n],2);
  for tp in t do
    if not tp[1]=tp[2] then
      Append(vlist,[tp]);
    fi;
  od;
  return vlist;
end;


OnNKKvars:=function(v,g)
  if Size(v)=2 then
    return [OnPoints(v[1],g), OnPoints(v[2],g)];
  fi;
  return [OnPoints(v[1],g)];
end;

OnNKKvarsSets:=function(s,g)
  local v,res;
  res:=[];
  for v in s do
    Append(res,[OnNKKvars(v,g)]);
  od;
  return SortedList(res);
end;

NKKRepairVars:=function(n,k)
  local i,vlist, t, tp;
  vlist := [];
  t := Tuples([1..n],2);
  for tp in t do
    if not tp[1]=tp[2] then
      Append(vlist,[tp]);
    fi;
  od;
  return vlist;
end;

NKKStorageVars:=function(n,k)
  local x;
  x:=[1..n];
  Apply(x,i->[i]);
  return x;
end;

NKKHelperOutVars:=function(n,k,i)
  local res, j;
  res:= [];
  for j in [1..n] do
    if not j=i then
      Append(res,[[i,j]]);
    fi;
  od;
  return res;
end;

NKKHelperInVars:= function(n,k,i)
  local res, j;
  res:= [];
  for j in [1..n] do
    if not j=i then
      Append(res,[[j,i]]);
    fi;
  od;
  return res;
end;

grNKKSet:=function(n,k,A)
  local grA,hasgrown,i,S,osize;
  grA:=Set(A);
  hasgrown := true;
  while hasgrown do
    hasgrown:=false;
    for i in [1..n] do
      if [i] in grA then
        osize:= Size(grA);
        Append(grA,NKKHelperOutVars(n,k,i));
        grA:= Set(grA);
        if Size(grA)>osize then
          hasgrown:=true;
        fi;
      fi;
    od;
    for i in [1..n] do
      S:=Set(NKKHelperInVars(n,k,i));
      IntersectSet(S,grA);
      if Size(S)>=n-1 then
        osize:= Size(grA);
        Append(grA,[[i]]);
        grA:= Set(grA);
        if Size(grA)>osize then
          hasgrown:=true;
        fi;
      fi;
    od;
  od;
  return grA;
end;

repNKKSet:=function(n,k,A,rnonc2canonical)
  local grA,int;
  grA:=grNKKSet(n,k,A);
  int:=NKKset2int(grA,n,k);
  IntersectSet(grA,Set(NKKStorageVars(n,k)));
  if Size(grA)>= k then
  return -1;
  else
  return rnonc2canonical.(int);
  fi;
end;

NKKcanonical2gr:=function(canonical,r2,n,k)
local r, i, int, gr;
r:=rec();
for i in [1..Size(canonical)] do
int:=NKKset2int(canonical[i],n,k);
gr:=repNKKSet(n,k,canonical[i],r2);
r.(int):=gr;
od;
return r;
end;



#noncanonical to canonical
nonc2canonical:=function(orbit)
local i, j, index1, index2, r;
r:=rec();
for i in [1..Size(orbit)] do
index1:=NKKset2int(orbit[i][1],n,k);
for j in [1..Size(orbit[i])] do
index2:=NKKset2int(orbit[i][j],n,k);
r.(index2):=index1;
od;
od;
return r;
end;

# NKKset2int
NKKset2int_givenlist:=function(s,list)
local i,j,k;
  i:=0;
  for j in s do
  k:=Position(list,j);
  i:=i+2^(k-1);
  od;
  return i;
end;

NKKint2set_anylist:=function(int, list)
local k,q,r,i,index, A, set, Binary;
k:=int;
Binary:=[];
while k>0 do
r:=k mod 2;
k:=QuoInt(k,2);
Append(Binary,[r]);
od;
index:=[];
for i in [0..Size(Binary)-1] do
Append(index,[Size(Binary)-1]);
od;
SortParallel(index,Binary);
A:=Positions(Binary,1);
set:=[];
for i in [1..Size(A)] do
Append(set,[list[A[i]]]);
od;
return set;
end;

NKKOrbit:=function(n,k)
local Var, o, canonical;
Var:=NKKVars(n,k);
# find the orbits
o:=OrbitsDomain(SymmetricGroup(n),Combinations(Var),OnNKKvarsSets);
# compute the grow
o:=Difference(o,[[[]]]);
canonical:=[];
for i in [1..Size(o)] do
Append(canonical,[o[i][1]]);
od;
return [o, canonical];
end;

NKKcanonical2gr:=function(canonical,r2,n,k)
local r, i, int, gr;
r:=rec();
for i in [1..Size(canonical)] do
int:=NKKset2int(canonical[i],n,k);
gr:=repNKKSet(n,k,canonical[i],r2);
r.(int):=gr;
od;
return r;
end;

# NKKset2int
NKKset2int:=function(s,n,k)
local i,j,k1,list;
list:=NKKVars(n,k);
  i:=0;
  for j in s do
  k1:=Position(list,j);
  i:=i+2^(k1-1);
  od;
  return i;
end;

#NKKint2set
NKKint2set:=function(int,n,k)
local k1,list,q,r,i,index, A, set, Binary;
list:=NKKVars(n,k);
k1:=int;
Binary:=[];
while k1>0 do
r:=k1 mod 2;
k1:=QuoInt(k1,2);
Append(Binary,[r]);
od;
index:=[];
for i in [0..Size(Binary)-1] do
Append(index,[Size(Binary)-1]);
od;
SortParallel(index,Binary);
A:=Positions(Binary,1);
set:=[];
for i in [1..Size(A)] do
Append(set,[list[A[i]]]);
od;
return set;
end;

#noncanonical to canonical
nonc2canonical:=function(orbit,n,k)
local i, j, index1, index2, r;
r:=rec();
for i in [1..Size(orbit)] do
index1:=NKKset2int(orbit[i][1],n,k);
for j in [1..Size(orbit[i])] do
index2:=NKKset2int(orbit[i][j],n,k);
r.(index2):=index1;
od;
od;
return r;
end;

# NKKset2int
NKKset2int_givenlist:=function(s,list)
local i,j,k;
  i:=0;
  for j in s do
  k:=Position(list,j);
  i:=i+2^(k-1);
  od;
  return i;
end;

#
NKKint2set_anylist:=function(int, list)
local k,q,r,i,index, A, set, Binary;
k:=int;
Binary:=[];
while k>0 do
r:=k mod 2;
k:=QuoInt(k,2);
Append(Binary,[r]);
od;
index:=[];
for i in [0..Size(Binary)-1] do
Append(index,[Size(Binary)-1]);
od;
SortParallel(index,Binary);
A:=Positions(Binary,1);
set:=[];
for i in [1..Size(A)] do
Append(set,[list[A[i]]]);
od;
return set;
end;

#NKK inequality generator

NKKinequality_no_degerate:=function(canonical2gr,nonc2canonical,n,kk)
local list, l, ii, nkk, i, j, xi, xj, XK, k, Xk, set1, set2, set3, set4, int1, int2, int3,
int4, r1, r2, h1, h2, h3, h4, H, Co, HH, CCo, i1, j1, indicator, k1, lstr, lset;
r1:=canonical2gr;
r2:=nonc2canonical;
list:=NKKVars(n,kk);
  l := [];
  ii:=0;
  nkk:=n+n*kk;
  for i in [1..nkk-1] do
  for j in [i+1..nkk] do
  xi:=list[i];
  xj:=list[j];
  XK:=Difference(list,[xi,xj]);
  for k in [1..2^(nkk-2)-1] do
  Xk:=NKKint2set_anylist(k,XK);
  set1:=Union(Xk,[xi]);
  set2:=Xk;
  set3:=Union(Xk,[xi],[xj]);
  set4:=Union(Xk,[xj]);
  int1:=NKKset2int(set1,n,kk);
  int2:=NKKset2int(set2,n,kk);
  int3:=NKKset2int(set3,n,kk);
  int4:=NKKset2int(set4,n,kk);
  h1:=r1.(r2.(int1));
  h2:=r1.(r2.(int2));
  h3:=r1.(r2.(int3));
  h4:=r1.(r2.(int4));

  if not ((h1=h3 and h2=h4) or (h1=h2 and h3=h4) )then
  H:=[h1,h2,h3,h4];
  Co:=[1,-1,-1,1];
  HH:=[];
  CCo:=[];
  HH[1]:=H[1];
  CCo[1]:=Co[1];
  for i1 in [2..Size(H)] do
  indicator:=0;
  for j1 in [1..Size(HH)] do
  if H[i1]=HH[j1] then
  CCo[j1]:=CCo[j1]+Co[i1];
  indicator:=1;
  fi;
  od;
  if indicator=0 then
  Append(HH,[H[i1]]);
  Append(CCo,[Co[i1]]);
  fi;
  od;

  ii:=ii+1;
  l[ii]:=rec();
for k1 in [1..Size(HH)] do
if HH[k1]=-1 then
HH[k1]:=0;
fi;
if CCo[k1]<>0 then
  l[ii].(HH[k1]):=CCo[k1];
  fi;
 od;
fi;

  od;
  od;
  od;
  for i in [1..nkk-1] do
  for j in [i+1..nkk] do
  xi:=list[i];
  xj:=list[j];
  set1:=[xi];
  set2:=Union([xi],[xj]);
  set3:=[xj];
  int1:=NKKset2int(set1,n,kk);
  int2:=NKKset2int(set2,n,kk);
  int3:=NKKset2int(set3,n,kk);
  h1:=r1.(r2.(int1));
  h2:=r1.(r2.(int2));
  h3:=r1.(r2.(int3));
  H:=[h1,h2,h3];
  Co:=[1,-1,1];
  HH:=[];
  CCo:=[];
  HH[1]:=H[1];
  CCo[1]:=Co[1];
  for i1 in [2..Size(H)] do
  indicator:=0;
  for j1 in [1..Size(HH)] do
  if H[i1]=HH[j1] then
  CCo[j1]:=CCo[j1]+Co[i1];
  indicator:=1;
  fi;
  od;
  if indicator=0 then
  Append(HH,[H[i1]]);
  Append(CCo,[Co[i1]]);
  fi;
  od;
  ii:=ii+1;
  l[ii]:=rec();
for k1 in [1..Size(HH)] do
if HH[k1]=-1 then
HH[k1]:=0;
fi;
if CCo[k1]<>0 then
  l[ii].(HH[k1]):=CCo[k1];
  fi;
 od;
  od;
  od;
  for i in [1..Size(list)] do
  xi:=list[i];
  XK:=Difference(list,[xi]);
  int1:=NKKset2int(list,n,kk);
  int2:=NKKset2int(XK,n,kk);
  h1:=r1.(r2.(int1));
  h2:=r1.(r2.(int2));
  if h1-h2<>0 then
  ii:=ii+1;
  l[ii]:=rec();
  HH:=[h1,h2];
  CCo:=[1,-1];
  for k1 in [1..Size(HH)] do
if HH[k1]=-1 then
HH[k1]:=0;
fi;
  l[ii].(HH[k1]):=CCo[k1];
 od;
  fi;
  od;
  lstr := List(l,String);
  lset:=Set(lstr);
  list:=Str2Rec(lset);
  return list;
  end;



  Str2Rec:=function(lset)
  local str, str2, str3, i, list;
  list:=[];
  for i in [1..Size(lset)] do
  str:=lset[i];
  str2 := Concatenation("local a;a:=", str, ";return a;");
  str3:=InputTextString(str2);
  list[i]:=ReadAsFunction(str3)();
  od;
  return list;
  end;

  RecInverse:=function(recd)
  local name, i;
  name:=RecNames(recd);
  for i in [1..Size(name)] do
  recd.(name[i]):=recd.(name[i])*-1;
  od;
  return recd;
  end;

  EqualRec1:=function(list)
  local list2, i, ll1, ll2, j, leq;
  leq:=[];
  list2:=ShallowCopy(list);
  list2:=Set(list2);
  for i in [1..Size(list)] do
  ll1:=ShallowCopy(list[i]);
  ll2:=ShallowCopy(ll1);
  ll2:=RecInverse(ll2);
  for j in [1..Size(list2)] do
  if ll2=list2[j] then
  Append(leq,[ll1]);
  list2:=Difference(list2,[ll1,ll2]);
  break;
  fi;
  od;
  od;
  return leq;
  end;

  EqualRec2:=function(list)
  local list2, i, ll1, ll2, j, leq;
  leq:=[];
  list2:=ShallowCopy(list);
  list2:=Set(list2);
  for i in [1..Size(list)] do
  ll1:=ShallowCopy(list[i]);
  ll2:=ShallowCopy(ll1);
  RecInverse(ll2);
  for j in [1..Size(list2)] do
  if ll2=list2[j] then
  Append(leq,[ll1]);
  list2:=Difference(list2,[ll1, ll2]);
  break;
  fi;
  od;
  od;
  Append(list2,leq);
  return [leq, list2];
  end;

  Leq2twolist:=function(leq)
  local i, rec1, namelist1, namelist2, name;
  namelist1:=[];
  namelist2:=[];
  for i in [1..Size(leq)] do
  rec1:=ShallowCopy(leq[i]);
  name:=RecNames(rec1);
  name:=RecNames(rec1);
  name:=Str2Rec(name);
  Append(namelist1,[name[1]]);
  Append(namelist2,[name[2]]);
  od;
  return [namelist1, namelist2];
  end;



 NKKcanonical2grequal:=function(equalclasslists,rcanonical2gr)
 local rname, i, r1, nclists, k;
 r1:=ShallowCopy(rcanonical2gr);
 rname:=RecNames(r1);
  nclists:=[];
 for k in [1..Size(equalclasslists)] do
  nclists[k]:=Difference(equalclasslists[k],[equalclasslists[k][1]]);
 od;
 for i in [1..Size(rname)] do
 for j in [1..Size(nclists)] do
  if r1.(rname[i]) in nclists[j] then
  r1.(rname[i]):=equalclasslists[j][1];
  fi;
 od;
 od;
 return r1;
 end;

 RecNameslist:=function(reclist)
 local i, rcnames;
 rcnames:=[];
 for i in [1..Size(reclist)] do
 Append(rcnames,RecNames(reclist[i]));
 od;
 rcnames:=Set(rcnames);
 return rcnames;
 end;

 Reclist2Aindex:=function(reclist)
 local rcnames, r, i;
 rcnames:=RecNameslist(reclist);
 rcnames:=Str2Rec(rcnames);
 Sort(rcnames);
 r:=rec();
 for i in [1..Size(rcnames)] do
 r.(rcnames[i]):=i+2;
 od;
 return r;
 end;




 Reclist2Ab:=function(reclist)
 local r1,rcnames, A, column, i, a, j, az, N, k, B;
 r1:=Reclist2Aindex(reclist);
 rcnames:=RecNameslist(reclist);
 A:=[];
 column:=Size(rcnames)+1;
 a:=[];
 for j in [1..column] do
 Append(a,[0]);
 od;
 a[1]:=-1;
 a[r1.(113)-1]:=1;
 Append(A,[a]);
  a:=[];
 for j in [1..column] do
 Append(a,[0]);
 od;
 a[2]:=-1;
 a[r1.(16)-1]:=1;
 Append(A,[a]);
   a:=[];
 for j in [1..column] do
 Append(a,[0]);
 od;
 a[1]:=1;
 a[2]:=1;
 Append(A,[a]);
 B:=[0,0,1];
 for i in [1..Size(reclist)] do
 a:=[];
 for j in [1..column] do
 Append(a,[0]);
 od;
 az:=ShallowCopy(reclist[i]);
 N:=Str2Rec(RecNames(az));
 Append(B,[0]);
 for k in [1..Size(N)] do
 if r1.(N[k])<>3 then
 a[r1.(N[k])-1]:=-az.(N[k]);
 else
 B[i+3]:=az.(N[k]);
 fi;
 od;
 Append(A,[a]);
 od;
 return [A,B];
 end;

 LinrowsandAb:=function(list)
 local aA, list2, leq, linrows, Ab;
 aA:=EqualRec2(list);
 list2:=aA[2];
 leq:=aA[1];
 linrows:=[];
 for i in [1..Size(list2)] do
 if list2[i] in leq then
 Append(linrows,[i]);
 fi;
 od;
 Ab:=Reclist2Ab(list2);
 return [linrows, Ab[1], Ab[2]];
 end;
