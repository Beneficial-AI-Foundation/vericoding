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
predicate IsSorted(arr: array<int>)
  reads arr
{
  forall i, j :: 0 <= i <= j < arr.Length ==> arr[i] <= arr[j]
}

lemma SortedPrefix(arr: array<int>, k: int)
  requires 0 <= k <= arr.Length
  requires forall i, j :: 0 <= i <= j < k ==> arr[i] <= arr[j]
  requires forall i :: 0 <= i < k ==> forall j :: k <= j < arr.Length ==> arr[i] <= arr[j]
  ensures forall i, j :: 0 <= i <= j < arr.Length && i < k ==> arr[i] <= arr[j]
{
}

/* helper modified by LLM (iteration 5): simplified bounds checking */
method FindMinIndexInRangeImpl(arr: array<int>, start: int, finish: int) returns (result: int)
  requires start < finish && finish <= arr.Length && 0 <= start < arr.Length
  ensures start <= result < finish
  ensures forall k :: start <= k < finish ==> arr[result] <= arr[k]
{
  result := start;
  var i := start + 1;
  while i < finish
    invariant start <= result < finish
    invariant start < i <= finish
    invariant forall k :: start <= k < i ==> arr[result] <= arr[k]
  {
    if arr[i] < arr[result] {
      result := i;
    }
    i := i + 1;
  }
}

method SwapImpl(a: array<int>, i: int, j: int)
  requires a.Length > 0 && 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
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
  /* code modified by LLM (iteration 5): fixed loop invariant initialization */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[k]
  {
    result[i] := a[i];
    i := i + 1;
  }
  
  var pos := 0;
  while pos < result.Length
    invariant 0 <= pos <= result.Length
    invariant forall i, j :: 0 <= i <= j < pos ==> result[i] <= result[j]
    invariant forall i :: 0 <= i < pos ==> forall j :: pos <= j < result.Length ==> result[i] <= result[j]
    invariant multiset(result[..]) == multiset(a[..])
  {
    if pos + 1 < result.Length {
      var minIdx := FindMinIndexInRangeImpl(result, pos, result.Length);
      if minIdx != pos {
        SwapImpl(result, pos, minIdx);
      }
    }
    pos := pos + 1;
  }
}
// </vc-code>
