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
  /* code modified by LLM (iteration 3): added assert to help prove loop invariant */
  var i := 0;
  var j := 0;
  result := new nat[a1.Length + a2.Length];
  var k := 0;

  while i < a1.Length && j < a2.Length
      invariant 0 <= i <= a1.Length && 0 <= j <= a2.Length && k == i + j
      invariant IsSorted(result[0..k])
      invariant multiset(result[0..k]) == multiset(a1[0..i]) + multiset(a2[0..j])
      invariant k > 0 ==> (i < a1.Length ==> result[k-1] <= a1[i])
      invariant k > 0 ==> (j < a2.Length ==> result[k-1] <= a2[j])
  {
      if a1[i] <= a2[j] {
          result[k] := a1[i];
          i := i + 1;
      } else {
          result[k] := a2[j];
          j := j + 1;
      }
      k := k + 1;
  }

  // After the first loop, if we have remaining elements in a1, then j must be a2.Length
  if i < a1.Length {
      assert j == a2.Length;
  }

  while i < a1.Length
      invariant 0 <= i <= a1.Length && j == a2.Length && k == i + j
      invariant IsSorted(result[0..k])
      invariant multiset(result[0..k]) == multiset(a1[0..i]) + multiset(a2[0..j])
      invariant k > 0 ==> (i < a1.Length ==> result[k-1] <= a1[i])
  {
      result[k] := a1[i];
      i := i + 1;
      k := k + 1;
  }

  while j < a2.Length
      invariant 0 <= j <= a2.Length && i == a1.Length && k == i + j
      invariant IsSorted(result[0..k])
      invariant multiset(result[0..k]) == multiset(a1[0..i]) + multiset(a2[0..j])
      invariant k > 0 ==> (j < a2.Length ==> result[k-1] <= a2[j])
  {
      result[k] := a2[j];
      j := j + 1;
      k := k + 1;
  }
}
// </vc-code>
