method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
  assume{:axiom} false;
}

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}

// <vc-helpers>
lemma CountLemma(arr: seq<int>, value: int, start: int, end: int)
  requires 0 <= start <= end <= |arr|
  ensures count(arr, value) == count(arr[..start], value) + count(arr[start..end], value) + count(arr[end..], value)
{}

lemma SliceLemma<T>(arr: array<T>, start: int, end: int) 
  requires 0 <= start <= end <= arr.Length
  ensures arr[start..end] == arr[..][start..end]
{}

lemma MultiSetLemma(arr: array<int>, i: int, j: int, k: int, l: int)
  requires 0 <= i < j < k < l <= arr.Length
  ensures multiset(arr[..]) == multiset(arr[..i] + arr[i..j] + arr[j..k] + arr[k..l] + arr[l..])
{
}

lemma SwapPreservesOrder(arr: array<int>, i: int, j: int, ghost original: seq<int>)
  requires arr.Length > 0 && 0 <= i < arr.Length && 0 <= j < arr.Length
  requires multiset(arr[..]) == multiset(original)
  requires forall n, m :: 0 <= n < m < arr.Length && arr[n] != 0 && arr[m] != 0 ==>
            n < m
  ensures multiset(arr[..]) == multiset(original)
  ensures forall n, m :: 0 <= n < m < arr.Length && original[n] != 0 && original[m] != 0 ==>
            n < m
{
}

predicate IsOrderPreserved(original: seq<int>, current: seq<int>)
  requires |original| == |current|
{
  multiset(original) == multiset(current) &&
  forall n, m :: 0 <= n < m < |original| && original[n] != 0 && original[m] != 0 ==>
    exists k, l :: 0 <= k < l < |current| && current[k] == original[n] && current[l] == original[m]
}

lemma OrderPreservationHelper(original: seq<int>, current: seq<int>, i: int, j: int)
  requires |original| == |current| && 0 <= i <= j <= |current|
  requires forall n, m :: 0 <= n < m < |original| && original[n] != 0 && original[m] != 0 ==>
            exists k, l :: 0 <= k < l < |current| && current[k] == original[n] && current[l] == original[m]
  requires forall k :: 0 <= k < i ==> current[k] != 0
  requires forall k :: i <= k < j ==> current[k] == 0
  ensures forall n, m :: 0 <= n < m < |original| && original[n] != 0 && original[m] != 0 ==>
            exists k, l :: 0 <= k < l < |current| && current[k] == original[n] && current[l] == original[m]
{
}
// </vc-helpers>

// <vc-spec>
method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    //ensures IsOrderPreserved(arr[..], old(arr[..]))
    // Number of zeros is preserved
// </vc-spec>
// <vc-code>
{
  var left := 0;
  var right := 0;
  ghost var original := arr[..];
  
  while right < arr.Length
    invariant 0 <= left <= right <= arr.Length
    invariant forall i :: 0 <= i < left ==> arr[i] != 0
    invariant forall i :: left <= i < right ==> arr[i] == 0
    invariant multiset(arr[..]) == multiset(original)
    invariant forall n, m :: 0 <= n < m < arr.Length && original[n] != 0 && original[m] != 0 ==>
                exists k, l :: 0 <= k < l < arr.Length && arr[k] == original[n] && arr[l] == original[m]
  {
    if arr[right] != 0 {
      swap(arr, left, right);
      left := left + 1;
    }
    right := right + 1;
  }
}
// </vc-code>

