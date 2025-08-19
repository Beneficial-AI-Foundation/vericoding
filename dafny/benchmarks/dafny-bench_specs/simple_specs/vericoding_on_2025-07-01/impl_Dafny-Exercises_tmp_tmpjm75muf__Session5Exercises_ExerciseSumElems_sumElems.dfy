//ATOM

function SumL(s:seq<int>):int
{
  if (s==[]) then 0
  else s[0]+SumL(s[1..])
}

//ATOM

function SumV(v:array<int>,c:int,f:int):int
 requires 0<=c<=f<=v.Length
 reads v
 {SumR(v[c..f])}

//ATOM

function SumR(s:seq<int>):int
{
  if (s==[]) then 0
  else SumR(s[..|s|-1])+s[|s|-1]
}


// SPEC
 

method sumElems(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[..])
//ensures sum==SumV(v,0,v.Length)

{
}