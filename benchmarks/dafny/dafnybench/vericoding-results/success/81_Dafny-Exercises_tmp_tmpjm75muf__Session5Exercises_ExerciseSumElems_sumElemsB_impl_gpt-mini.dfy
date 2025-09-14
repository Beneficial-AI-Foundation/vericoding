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
lemma SumV_succ(v: array<int>, c: int, f: int)
  requires 0 <= c <= f < v.Length
  ensures SumV(v, c, f+1) == SumV(v, c, f) + v[f]
{
  var s := v[c..f+1];
  assert s != [];
  assert s[..|s|-1] == v[c..f];
  assert s[|s|-1] == v[f];
  calc {
    SumV(v, c, f+1);
    == { }
    SumR(s);
    == { }
    SumR(s[..|s|-1]) + s[|s|-1];
    == { }
    SumR(v[c..f]) + v[f];
    == { }
    SumV(v, c, f) + v[f];
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
  var i := 0;
  sum := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumV(v, 0, i)
  {
    SumV_succ(v, 0, i);
    sum := sum + v[i];
    i := i + 1;
  }
}
// </vc-code>

