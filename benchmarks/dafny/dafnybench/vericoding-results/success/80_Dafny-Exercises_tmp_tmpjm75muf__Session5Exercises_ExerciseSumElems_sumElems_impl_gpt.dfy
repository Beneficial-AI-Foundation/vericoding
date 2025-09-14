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
lemma SumR_Append(s: seq<int>, x: int)
  ensures SumR(s + [x]) == SumR(s) + x
{
  assert s + [x] != [];
  assert |s + [x]| == |s| + 1;
  assert |s + [x]| - 1 == |s|;
  assert (s + [x])[|s|] == x;
  assert (s + [x])[..|s|] == s;
  calc {
    SumR(s + [x]);
    == { }
    SumR((s + [x])[..|s + [x]| - 1]) + (s + [x])[|s + [x]| - 1];
    == { }
    SumR((s + [x])[..|s|]) + (s + [x])[|s|];
    == { }
    SumR(s) + x;
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
  var i := 0;
  sum := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[..i])
    decreases v.Length - i
  {
    var oldI := i;
    sum := sum + v[oldI];
    assert sum == SumR(v[..oldI]) + v[oldI];
    SumR_Append(v[..oldI], v[oldI]);
    assert sum == SumR(v[..oldI] + [v[oldI]]);
    i := oldI + 1;
    assert v[..i] == v[..oldI] + [v[oldI]];
    assert sum == SumR(v[..i]);
  }
  assert sum == SumR(v[..i]);
  assert i == v.Length;
  assert v[..i] == v[..];
  assert sum == SumR(v[..]);
}
// </vc-code>

