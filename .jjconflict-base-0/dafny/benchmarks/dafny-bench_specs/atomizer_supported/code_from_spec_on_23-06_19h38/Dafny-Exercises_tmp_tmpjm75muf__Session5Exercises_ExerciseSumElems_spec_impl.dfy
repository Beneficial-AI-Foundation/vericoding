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

// ATOM 
lemma concatLast(s:seq<int>,t:seq<int>)
requires t!=[]
ensures (s+t)[..|s+t|-1] == s+(t[..|t|-1])
{}

// ATOM 
lemma concatFirst(s:seq<int>,t:seq<int>)
requires s!=[]
ensures (s+t)[1..] == s[1..]+t
{}

lemma SumByPartsR(s:seq<int>,t:seq<int>)
ensures SumR(s+t) == SumR(s)+SumR(t)
{ 
  if (t==[])
  {
    assert s+t == s;
  }
  else if (s==[])
  {
    assert s+t==t;
  }   
  else
  { 
    calc == {
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

lemma SumByPartsL(s:seq<int>,t:seq<int>)
ensures SumL(s+t) == SumL(s)+SumL(t)
{
  if(t==[])
  {
    assert s+t == s;
  }
  else if(s==[])
  {
    assert s+t == t;
  }
  else
  {
    calc == {
      SumL(s+t);
      (s+t)[0] + SumL((s+t)[1..]);
      s[0] + SumL((s+t)[1..]);
      {concatFirst(s,t);}
      s[0] + SumL(s[1..] + t);
      {SumByPartsL(s[1..], t);}
      s[0] + SumL(s[1..]) + SumL(t);
      SumL(s) + SumL(t);
    }
  }
}

lemma equalSumR(s:seq<int>,i:int,j:int)
requires 0<=i<=j<=|s|
ensures  SumR(s[i..j])==SumL(s[i..j])
{
  if(i==j)
  {
    assert s[i..j] == [];
  }
  else
  {
    equalSumR(s, i, j-1);
    calc == {
      SumR(s[i..j]);
      SumR(s[i..j-1]) + s[j-1];
      SumL(s[i..j-1]) + s[j-1];
      SumL(s[i..j-1]) + SumL([s[j-1]]);
      {SumByPartsL(s[i..j-1], [s[j-1]]);}
      SumL(s[i..j-1] + [s[j-1]]);
      {assert s[i..j-1] + [s[j-1]] == s[i..j];}
      SumL(s[i..j]);
    }
  }
}

// ATOM 
lemma equalSumsV() 
ensures forall v:array<int>,i,j | 0<=i<=j<=v.Length :: SumR(v[i..j])==SumL(v[i..j])
{
  forall v:array<int>,i,j | 0<=i<=j<=v.Length
  ensures SumR(v[i..j])==SumL(v[i..j])
  {
    equalSumR(v[..],i,j);
  }
}

// ATOM 
function SumV(v:array<int>,c:int,f:int):int
requires 0<=c<=f<=v.Length
reads v
{
  SumR(v[c..f])
}

// ATOM 
lemma ArrayFacts<T>()
ensures forall v : array<T>  :: v[..v.Length] == v[..];
ensures forall v : array<T>  :: v[0..] == v[..];
ensures forall v : array<T>  :: v[0..v.Length] == v[..];
ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
{
  equalSumsV();
}

//IMPL sumElems
method sumElems(v:array<int>) returns (sum:int)
ensures sum==SumR(v[..])
{
  sum := 0;
  var i := 0;
  ArrayFacts();
  /* code modified by LLM (iteration 2): Added base case assertions for empty array slice */
  assert v[0..0] == [];
  assert SumR([]) == 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[0..i])
  {
    /* code modified by LLM (iteration 2): Added assertions to help verification with array slicing and SumR properties */
    assert v[0..i+1] == v[0..i] + [v[i]];
    assert SumR([v[i]]) == v[i];
    SumByPartsR(v[0..i], [v[i]]);
    assert SumR(v[0..i] + [v[i]]) == SumR(v[0..i]) + SumR([v[i]]);
    sum := sum + v[i];
    i := i + 1;
  }
  /* code modified by LLM (iteration 2): Added final assertion to connect loop invariant to postcondition */
  assert i == v.Length;
  assert v[0..v.Length] == v[..];
  assert sum == SumR(v[0..v.Length]);
}

//IMPL sumElemsB  
method sumElemsB(v:array<int>) returns (sum:int)
ensures sum==SumR(v[0..v.Length])
{
  sum := 0;
  var i := 0;
  ArrayFacts();
  /* code modified by LLM (iteration 2): Added base case assertions for empty array slice */
  assert v[0..0] == [];
  assert SumR([]) == 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[0..i])
  {
    /* code modified by LLM (iteration 2): Added assertions to help verification with array slicing and SumR properties */
    assert v[0..i+1] == v[0..i] + [v[i]];
    assert SumR([v[i]]) == v[i];
    SumByPartsR(v[0..i], [v[i]]);
    assert SumR(v[0..i] + [v[i]]) == SumR(v[0..i]) + SumR([v[i]]);
    sum := sum + v[i];
    i := i + 1;
  }
  /* code modified by LLM (iteration 2): Added final assertion to ensure postcondition is satisfied */
  assert i == v.Length;
  assert sum == SumR(v[0..v.Length]);
}