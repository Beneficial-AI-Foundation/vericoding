// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MergeSorted(a1: array<nat>, a2: array<nat>) returns (result: array<nat>)
    requires IsSorted(a1[..])
    requires IsSorted(a2[..])
    ensures IsSorted(result[..])
    ensures multiset(result[..]) == multiset(a1[..]) + multiset(a2[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): proving postcondition by establishing i and j reach array lengths */
{
  result := new nat[a1.Length + a2.Length];
  var i := 0;
  var j := 0;
  var k := 0;
  
  while k < result.Length
    invariant 0 <= i <= a1.Length
    invariant 0 <= j <= a2.Length
    invariant k == i + j
    invariant k <= result.Length
    invariant IsSorted(result[..k])
    invariant multiset(result[..k]) == multiset(a1[..i]) + multiset(a2[..j])
    invariant i < a1.Length ==> forall x :: 0 <= x < k ==> result[x] <= a1[i]
    invariant j < a2.Length ==> forall x :: 0 <= x < k ==> result[x] <= a2[j]
    invariant k == result.Length ==> i == a1.Length && j == a2.Length
  {
    if i == a1.Length {
      result[k] := a2[j];
      j := j + 1;
    } else if j == a2.Length {
      result[k] := a1[i];
      i := i + 1;
    } else if a1[i] <= a2[j] {
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
