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
  /* code modified by LLM (iteration 5): Added invariant to relate previous element to current pointers ensuring sorted order maintenance */
  var n1 := a1.Length;
  var n2 := a2.Length;
  result := new nat[n1 + n2];
  var i := 0;
  var j := 0;
  var k := 0;
  while k < n1 + n2
    invariant 0 <= i <= n1 && 0 <= j <= n2 && k == i + j
    invariant if k > 0 then result[k-1] <= a1[i] && result[k-1] <= a2[j]
    invariant IsSorted(result[0..k])
    invariant multiset(result[0..k]) == multiset(a1[0..i]) + multiset(a2[0..j])
  {
    if i < n1 && (j >= n2 || a1[i] <= a2[j]) {
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
