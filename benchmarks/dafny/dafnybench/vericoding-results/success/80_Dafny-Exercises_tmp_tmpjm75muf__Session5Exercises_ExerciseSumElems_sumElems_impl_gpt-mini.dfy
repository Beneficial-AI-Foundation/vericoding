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
lemma SumR_prefix(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures SumR(s[..i+1]) == SumR(s[..i]) + s[i]
  decreases i
{
  if i == 0 {
    // s[..1] is sequence with single element s[0]
    assert s[..1] == [s[0]];
    // by definition of SumR
    assert SumR(s[..1]) == SumR(s[..0]) + s[0];
  } else {
    // length of s[..i+1] is i+1
    assert |s[..i+1]| == i + 1;
    // the prefix of length (i+1)-1 equals s[..i]
    assert (s[..i+1])[..|s[..i+1]|-1] == s[..i];
    // the last element of s[..i+1] is s[i]
    assert (s[..i+1])[|s[..i+1]|-1] == s[i];
    // unfold definition of SumR on s[..i+1]
    assert SumR(s[..i+1]) == SumR((s[..i+1])[..|s[..i+1]|-1]) + (s[..i+1])[|s[..i+1]|-1];
    // combine equalities to get the desired result
    assert SumR(s[..i+1]) == SumR(s[..i]) + s[i];
  }
}

lemma SumR_array_full(v: array<int>)
  ensures SumR(v[..v.Length]) == SumR(v[..])
{
  // v[..v.Length] is syntactically equal to v[..], but assert to help verifier
  assert v[..v.Length] == v[..];
  assert SumR(v[..v.Length]) == SumR(v[..]);
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
  var i := 0;
  sum := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[..i])
  {
    var j := i;
    // use the lemma before updating sum to relate prefixes
    SumR_prefix(v[..], j);
    sum := sum + v[j];
    i := j + 1;
    // update invariant: sum == SumR(v[..i])
    assert sum == SumR(v[..i]);
  }
  // at exit i == v.Length, relate SumR(v[..i]) to SumR(v[..])
  assert i == v.Length;
  SumR_array_full(v);
  assert sum == SumR(v[..]);
}
// </vc-code>

