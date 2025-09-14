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
/* helper modified by LLM (iteration 5): removed modifies clause from lemma */
function MinInRange(arr: seq<int>, start: int, end: int): int
  requires 0 <= start < end <= |arr|
  decreases end - start
{
  if start + 1 == end then arr[start]
  else if arr[start] <= MinInRange(arr, start + 1, end) then arr[start]
  else MinInRange(arr, start + 1, end)
}

lemma SwapPreservesMultiset(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(a[..]) == multiset(old(a[..])) + multiset{old(a[i]), old(a[j])} - multiset{old(a[i]), old(a[j])}
{
}
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
  /* code modified by LLM (iteration 5): fixed initial copy and loop invariants to properly establish multiset preservation */
  result := new int[a.Length];
  
  var k := 0;
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant result.Length == a.Length
    invariant forall idx :: 0 <= idx < k ==> result[idx] == a[idx]
    invariant multiset(result[..k]) == multiset(a[..k])
  {
    result[k] := a[k];
    k := k + 1;
  }
  
  var i := 0;
  while i < result.Length
    invariant 0 <= i <= result.Length
    invariant result.Length == a.Length
    invariant multiset(result[..]) == multiset(a[..])
    invariant forall x, y :: 0 <= x <= y < i ==> result[x] <= result[y]
    invariant forall x, y :: 0 <= x < i && i <= y < result.Length ==> result[x] <= MinInRange(result[..], i, result.Length)
  {
    if i < result.Length {
      var minIndex := FindMinIndexInRange(result, i, result.Length);
      if minIndex != i {
        Swap(result, i, minIndex);
      }
    }
    i := i + 1;
  }
}
// </vc-code>
