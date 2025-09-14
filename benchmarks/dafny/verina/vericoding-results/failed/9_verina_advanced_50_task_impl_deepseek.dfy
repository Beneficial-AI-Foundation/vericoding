// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add SumSeq function to resolve compilation errors */
function SumSeq(s: seq<nat>): nat
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method MergeSorted(a1: array<nat>, a2: array<nat>) returns (result: array<nat>)
    requires IsSorted(a1[..])
    requires IsSorted(a2[..])
    ensures IsSorted(result[..])
    ensures multiset(result[..]) == multiset(a1[..]) + multiset(a2[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Remove unnecessary SumSeq reference from ensures clause */
{
  var i := 0;
  var j := 0;
  var k := 0;
  result := new nat[a1.Length + a2.Length];
  
  while k < result.Length
    invariant 0 <= i <= a1.Length
    invariant 0 <= j <= a2.Length
    invariant k == i + j
    invariant IsSorted(result[0..k])
    invariant multiset(result[0..k]) == multiset(a1[0..i]) + multiset(a2[0..j])
    invariant (i > 0 && k > 0) ==> result[k-1] <= a1[i-1]
    invariant (j > 0 && k > 0) ==> result[k-1] <= a2[j-1]
  {
    if i < a1.Length && (j >= a2.Length || a1[i] <= a2[j]) {
      result[k] := a1[i];
      i := i + 1;
    } else {
      result[k] := a2[j];
      j := j + 1;
    }
    k := k + 1;
  }
}
// </vc-code>
