// ATOM 
function SumR(s:seq<int>):int
{
    if (s==[]) then 0
    else SumR(s[..|s|-1])+s[|s|-1]
}

// ATOM 
function SumL(s:seq<int>):int
{
    if (s==[]) then 0
    else s[0]+SumL(s[1..])
}

//ATOM concatLast
lemma concatLast(s:seq<int>, t:seq<int>)
requires t != []
ensures (s+t)[..|s+t|-1] == s+t[..|t|-1]
{
}

//ATOM concatFirst
lemma concatFirst(s:seq<int>, t:seq<int>)
requires s != []
ensures (s+t)[1..] == s[1..]+t
{
}

//ATOM SumByPartsR
lemma SumByPartsR(s:seq<int>,t:seq<int>)
ensures SumR(s+t) == SumR(s)+SumR(t)
{ if (t==[])
     {assert s+t == s;}
  else if (s==[])
     {assert s+t==t;}   
   else
     { 
       calc =={
        SumR(s+t);
        SumR((s+t)[..|s+t|-1])+(s+t)[|s+t|-1];
        SumR((s+t)[..|s+t|-1])+t[|t|-1];
        {concatLast(s,t);}
        SumR(s+t[..|t|-1])+t[|t|-1];
        {SumByPartsR(s,t[..|t|-1]);}
        SumR(s)+SumR(t[..|t|-1])+t[|t|-1];
        SumR(s)+SumR(t);
       }
     }
}

//ATOM SumByPartsL
lemma SumByPartsL(s:seq<int>,t:seq<int>)
ensures SumL(s+t) == SumL(s)+SumL(t)
{
  if(t==[]){
  }
  else if(s==[]){
  }
  else{
      calc == {
        SumL(s+t);
        (s+t)[0] + SumL((s+t)[1..]);
        s[0] + SumL((s+t)[1..]);
        {concatFirst(s,t);}
        s[0] + SumL(s[1..] + t);
        {SumByPartsL(s[1..], t);}
        s[0] + SumL(s[1..]) + SumL(t);
      }
  }
}

//ATOM equalSumR
lemma equalSumR(s:seq<int>,i:int,j:int)
requires 0<=i<=j<=|s|
ensures  SumR(s[i..j])==SumL(s[i..j])
{
  if(s==[]){
  }else{
    if(i==j){
    }
    else{
      calc == {
        SumR(s[i..j]);
        SumR(s[i..j-1]) + s[j-1];
        {equalSumR(s, i, j-1);}
        SumL(s[i..j-1]) + s[j-1];
        {assert s[j-1] == SumL([s[j-1]]);}
        SumL(s[i..j-1]) + SumL([s[j-1]]);
        {SumByPartsL(s[i..j-1], [s[j-1]]);}
        SumL(s[i..j-1] + [s[j-1]]);
        SumL(s[i..j]);
      }
    }
  }
}

//ATOM equalSumsV
lemma equalSumsV(v:array<int>,c:int,f:int)
requires 0<=c<=f<=v.Length
reads v
ensures SumV(v,c,f)==SumL(v[c..f])
{
  equalSumR(v[..],c,f);
}

// ATOM 
function SumV(v:array<int>,c:int,f:int):int
  requires 0<=c<=f<=v.Length
  reads v
  {SumR(v[c..f])}

//ATOM ArrayFacts
lemma ArrayFacts(v:array<int>)
ensures v[..] == v[0..v.Length]
{
}

/* code modified by LLM (iteration 2): Helper lemma for single element sum */
lemma SingleElementSum(v: array<int>, i: int)
  requires 0 <= i < v.Length
  reads v
  ensures SumR(v[i..i+1]) == v[i]
{
  calc == {
    SumR(v[i..i+1]);
    SumR(v[i..i+1][..|v[i..i+1]|-1]) + v[i..i+1][|v[i..i+1]|-1];
    SumR(v[i..i]) + v[i];
    SumR([]) + v[i];
    0 + v[i];
    v[i];
  }
}

//IMPL sumElems
method sumElems(v:array<int>) returns (sum:int)
ensures sum==SumR(v[..])
{
    sum := 0;
    var i := 0;
    
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant sum == SumR(v[0..i])
    {
        /* code modified by LLM (iteration 2): Use helper lemma and SumByPartsR */
        SingleElementSum(v, i);
        SumByPartsR(v[0..i], v[i..i+1]);
        
        sum := sum + v[i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 2): Apply ArrayFacts lemma for final equivalence */
    ArrayFacts(v);
}