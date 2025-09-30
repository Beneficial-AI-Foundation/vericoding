function SumR(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else SumR(s[..|s|-1])+s[|s|-1]
}

function SumL(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else s[0]+SumL(s[1..])
}


function SumV(v:array<int>,c:int,f:int):int
  requires 0<=c<=f<=v.Length
  reads v
  {
    SumR(v[c..f])
  }

// <vc-helpers>
lemma SumRProperty(s: seq<int>, i: int, sum: int)
  requires 0 <= i <= |s|
  ensures sum + SumR(s[i..]) == sum + SumR(s[i..])
{
  // Trivial lemma for clarity
}

lemma SumRStep(s: seq<int>, i: int, sum: int)
  requires 0 <= i < |s|
  ensures sum + s[i] + SumR(s[i+1..]) == sum + SumR(s[i..])
{
  if i == |s| - 1 {
    assert s[i..] == [s[i]];
    assert s[i+1..] == [];
    assert SumR(s[i..]) == SumR([s[i]]) == s[i] + SumR([]) == s[i];
    assert SumR(s[i+1..]) == SumR([]) == 0;
  } else {
    assert s[i..] == [s[i]] + s[i+1..];
    SumRConcat([s[i]], s[i+1..]);
  }
}

lemma SumRConcat(s1: seq<int>, s2: seq<int>)
  ensures SumR(s1 + s2) == SumR(s1) + SumR(s2)
{
  if s1 == [] {
    assert s1 + s2 == s2;
  } else if s2 == [] {
    assert s1 + s2 == s1;
  } else {
    var combined := s1 + s2;
    assert combined[..|combined|-1] == s1 + s2[..|s2|-1];
    assert combined[|combined|-1] == s2[|s2|-1];
    SumRConcat(s1, s2[..|s2|-1]);
  }
}
// </vc-helpers>

// <vc-spec>
method sumElems(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[..])
//ensures sum==SumV(v,0,v.Length)
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[..i])
  {
    assert v[..i+1] == v[..i] + [v[i]];
    SumRConcat(v[..i], [v[i]]);
    assert SumR(v[..i+1]) == SumR(v[..i]) + SumR([v[i]]);
    assert SumR([v[i]]) == v[i];
    
    sum := sum + v[i];
    i := i + 1;
  }
  
  assert i == v.Length;
  assert v[..i] == v[..v.Length] == v[..];
}
// </vc-code>

