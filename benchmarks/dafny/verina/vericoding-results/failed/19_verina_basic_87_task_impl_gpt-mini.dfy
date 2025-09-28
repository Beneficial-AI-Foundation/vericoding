// <vc-preamble>
method FindMinIndexInRange(arr: array<int>, start: int, finish: int) returns (result: int)
    requires 
        start <= finish &&
        finish <= arr.Length &&
        start < arr.Length
    ensures
        start <= result < finish
{
    // impl-start
    assume {:axiom} false;
    result := start;
    // impl-end
}

method Swap(a: array<int>, i: int, j: int)
    requires
        a.Length > 0 &&
        0 <= i < a.Length &&
        0 <= j < a.Length
    modifies a
    ensures
        a.Length == old(a.Length) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == old(a[j])) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[j] == old(a[i])) &&
        forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helper functions needed */
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i <= j < result.Length ==> result[i] <= result[j]) &&
        multiset(result[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): selection sort implemented using sequences */
  var rem := a[..];
  var resSeq: seq<int> := [];
  while |rem| > 0
    invariant multiset(resSeq + rem) == multiset(a[..])
    invariant forall p, q :: 0 <= p <= q < |resSeq| ==> resSeq[p] <= resSeq[q]
  {
    var m := 0;
    var k := 1;
    while k < |rem|
      invariant 0 <= m < |rem| && 0 <= k <= |rem|
      invariant forall t :: 0 <= t < k ==> rem[m] <= rem[t]
    {
      if rem[k] < rem[m] {
        m := k;
      }
      k := k + 1;
    }
    resSeq := resSeq + [rem[m]];
    rem := rem[0..m] + rem[m+1..];
  }
  var rarr := new int[|resSeq|];
  var ii := 0;
  while ii < |resSeq|
    invariant 0 <= ii <= |resSeq|
    invariant forall t :: 0 <= t < ii ==> rarr[t] == resSeq[t]
  {
    rarr[ii] := resSeq[ii];
    ii := ii + 1;
  }
  result := rarr;
}
// </vc-code>
