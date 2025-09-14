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
  {SumR(v[c..f])}

// <vc-helpers>
lemma SumREquivalence(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures SumR(s[0..i]) == if i == 0 then 0 else SumR(s[0..i-1]) + s[i-1]
{
  if i == 0 {
    assert s[0..0] == [];
  } else {
    assert s[0..i] == s[0..i-1] + [s[i-1]];
    assert s[0..i][..|s[0..i]|-1] == s[0..i-1];
    assert s[0..i][|s[0..i]|-1] == s[i-1];
  }
}

lemma SumRInvariant(v: array<int>, i: int, sum: int)
  requires 0 <= i <= v.Length
  requires sum == SumR(v[0..i])
  ensures sum + SumR(v[i..v.Length]) == SumR(v[0..v.Length])
{
  if i == v.Length {
    assert v[i..v.Length] == [];
    assert SumR(v[i..v.Length]) == 0;
    assert v[0..i] == v[0..v.Length];
  } else {
    var fullSeq := v[0..v.Length];
    var leftPart := v[0..i];
    var rightPart := v[i..v.Length];
    assert fullSeq == leftPart + rightPart;
    SumRConcatenation(leftPart, rightPart);
  }
}

lemma SumRConcatenation(s1: seq<int>, s2: seq<int>)
  ensures SumR(s1 + s2) == SumR(s1) + SumR(s2)
{
  if s2 == [] {
    assert s1 + s2 == s1;
  } else if s1 == [] {
    assert s1 + s2 == s2;
  } else {
    var combined := s1 + s2;
    assert combined[..|combined|-1] == s1 + s2[..|s2|-1];
    assert combined[|combined|-1] == s2[|s2|-1];
    SumRConcatenation(s1, s2[..|s2|-1]);
  }
}

lemma SumRUpdateLemma(v: array<int>, i: int, sum: int)
  requires 0 <= i < v.Length
  requires sum == SumR(v[0..i])
  ensures sum + v[i] == SumR(v[0..i+1])
{
  if i == 0 {
    assert v[0..0] == [];
    assert SumR(v[0..0]) == 0;
    assert v[0..1] == [v[0]];
    assert SumR(v[0..1]) == v[0];
  } else {
    assert v[0..i+1][..|v[0..i+1]|-1] == v[0..i];
    assert v[0..i+1][|v[0..i+1]|-1] == v[i];
    assert SumR(v[0..i+1]) == SumR(v[0..i]) + v[i];
  }
}
// </vc-helpers>

// <vc-spec>
method sumElemsB(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[0..i])
  {
    SumRUpdateLemma(v, i, sum);
    sum := sum + v[i];
    i := i + 1;
  }
}
// </vc-code>

