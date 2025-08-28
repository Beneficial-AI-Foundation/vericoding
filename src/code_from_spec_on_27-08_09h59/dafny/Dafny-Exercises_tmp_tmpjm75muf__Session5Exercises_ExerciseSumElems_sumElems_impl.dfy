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
lemma SumREmpty()
  ensures SumR([]) == 0
{
}

lemma SumRSingle(x: int)
  ensures SumR([x]) == x
{
}

lemma SumRAppend(s: seq<int>, x: int)
  ensures SumR(s + [x]) == SumR(s) + x
{
  if s == [] {
    assert s + [x] == [x];
    assert SumR(s + [x]) == SumR([x]) == x;
    assert SumR(s) + x == 0 + x == x;
  } else {
    var s' := s + [x];
    assert s'[..|s'|-1] == s;
    assert s'[|s'|-1] == x;
    assert SumR(s') == SumR(s) + x;
  }
}

lemma SumRInductive(v: array<int>, i: int)
  requires 0 <= i <= v.Length
  ensures SumR(v[..i]) == if i == 0 then 0 else SumR(v[..i-1]) + v[i-1]
{
  if i == 0 {
    assert v[..0] == [];
  } else {
    assert v[..i] == v[..i-1] + [v[i-1]];
    SumRAppend(v[..i-1], v[i-1]);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method sumElems(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[..])
//ensures sum==SumV(v,0,v.Length)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  sum := 0;
  var i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[..i])
  {
    SumRInductive(v, i + 1);
    sum := sum + v[i];
    i := i + 1;
  }
  
  assert v[..v.Length] == v[..];
}
// </vc-code>
