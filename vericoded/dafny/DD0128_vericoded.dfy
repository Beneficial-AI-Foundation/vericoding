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
lemma SumRConcat(s1: seq<int>, s2: seq<int>)
  ensures SumR(s1 + s2) == SumR(s1) + SumR(s2)
{
  if s2 == [] {
    assert s1 + s2 == s1;
  } else {
    var s2' := s2[..|s2|-1];
    var last := s2[|s2|-1];
    assert s2 == s2' + [last];
    assert s1 + s2 == (s1 + s2') + [last];
    assert SumR(s1 + s2) == SumR(s1 + s2') + last;
    SumRConcat(s1, s2');
    assert SumR(s1 + s2') == SumR(s1) + SumR(s2');
    assert SumR(s2) == SumR(s2') + last;
  }
}

lemma SumRSingle(x: int)
  ensures SumR([x]) == x
{
  assert [x] == [] + [x];
  assert SumR([x]) == SumR([]) + x == 0 + x == x;
}

lemma SumRPrefix(v: array<int>, i: int)
  requires 0 <= i < v.Length
  ensures SumR(v[0..i+1]) == SumR(v[0..i]) + v[i]
{
  assert v[0..i+1] == v[0..i] + [v[i]];
  SumRSingle(v[i]);
  SumRConcat(v[0..i], [v[i]]);
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
    SumRPrefix(v, i);
    sum := sum + v[i];
    i := i + 1;
  }
  
  assert i == v.Length;
  assert v[0..v.Length] == v[0..v.Length];
}
// </vc-code>

