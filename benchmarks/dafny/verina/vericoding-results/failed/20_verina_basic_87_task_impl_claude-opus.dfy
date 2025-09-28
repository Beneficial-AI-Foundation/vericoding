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
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
  {
    result[i] := a[i];
    i := i + 1;
  }
  
  i := 0;
  while i < result.Length - 1
    invariant 0 <= i <= result.Length
    invariant forall k, l :: 0 <= k <= l < i ==> result[k] <= result[l]
    invariant forall k, l :: 0 <= k < i <= l < result.Length ==> result[k] <= result[l]
    invariant multiset(result[..]) == multiset(a[..])
  {
    var minIndex := i;
    var j := i + 1;
    while j < result.Length
      invariant i < j <= result.Length
      invariant i <= minIndex < j
      invariant forall k :: i <= k < j ==> result[minIndex] <= result[k]
    {
      if result[j] < result[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      var temp := result[i];
      result[i] := result[minIndex];
      result[minIndex] := temp;
    }
    i := i + 1;
  }
}
// </vc-code>
