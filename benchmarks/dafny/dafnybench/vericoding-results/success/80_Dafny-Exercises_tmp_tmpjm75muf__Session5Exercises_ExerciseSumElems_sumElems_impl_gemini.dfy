// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): expanded proof of SumR_unfold */
lemma SumR_unfold(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures SumR(s[..i+1]) == SumR(s[..i]) + s[i]
{
  var t := s[..i+1];
  assert s[..i+1][|s[..i+1]|-1] == s[i];
  assert s[..i+1][..|s[..i+1]|-1] == s[..i];
}
// </vc-helpers>

// <vc-spec>
method sumElems(v:array<int>) returns (sum:int)
ensures sum==SumR(v[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): added a check on loop exit to help prove postcondition */
  sum := 0;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[..i])
  {
    SumR_unfold(v[..], i);
    sum := sum + v[i];
    i := i + 1;
  }
  assert v[..] == v[..v.Length];
}
// </vc-code>
