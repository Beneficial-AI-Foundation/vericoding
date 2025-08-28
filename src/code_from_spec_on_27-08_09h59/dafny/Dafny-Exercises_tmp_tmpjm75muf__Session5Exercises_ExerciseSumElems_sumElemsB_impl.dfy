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
lemma SumRAppendLast(s: seq<int>, x: int)
  ensures SumR(s + [x]) == SumR(s) + x
{
  if s == [] {
    assert s + [x] == [x];
    assert SumR([x]) == SumR([]) + x;
  } else {
    var s' := s + [x];
    assert s'[..|s'|-1] == s;
    assert s'[|s'|-1] == x;
    assert SumR(s') == SumR(s) + x;
  }
}

lemma SumRSliceProperty(v: array<int>, i: int, j: int)
  requires 0 <= i <= j <= v.Length
  ensures SumR(v[i..j]) == SumV(v, i, j)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method sumElemsB(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[0..v.Length])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  sum := 0;
  var i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[0..i])
  {
    SumRAppendLast(v[0..i], v[i]);
    assert v[0..i+1] == v[0..i] + [v[i]];
    sum := sum + v[i];
    i := i + 1;
  }
}
// </vc-code>
