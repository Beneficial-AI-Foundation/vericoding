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
{
  result := new nat[a1.Length + a2.Length];
  var i := 0;
  var j := 0;
  var k := 0;
  while i < a1.Length || j < a2.Length
    invariant 0 <= i <= a1.Length
    invariant 0 <= j <= a2.Length
    invariant k == i + j
    invariant IsSorted(result[..k])
    invariant multiset(result[..k]) == multiset(a1[..i]) + multiset(a2[..j])
    invariant forall x :: 0 <= x < k && i < a1.Length ==> result[x] <= a1[i]
    invariant forall x :: 0 <= x < k && j < a2.Length ==> result[x] <= a2[j]
    decreases a1.Length + a2.Length - k
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
