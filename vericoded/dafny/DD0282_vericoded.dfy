

// <vc-helpers>
ghost predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

lemma SwapMultiset(a: seq<int>, i: int, j: int)
  requires 0 <= i < |a| && 0 <= j < |a|
  ensures multiset(a[i := a[j]][j := a[i]]) == multiset(a)
{
  var swapped := a[i := a[j]][j := a[i]];
  assert swapped[i] == a[j];
  assert swapped[j] == a[i];
  assert forall k :: 0 <= k < |a| && k != i && k != j ==> swapped[k] == a[k];
}
// </vc-helpers>

// <vc-spec>
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
// </vc-spec>
// <vc-code>
{
  var n := Array.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n
    invariant multiset(old(Array[..])) == multiset(Array[..])
    invariant forall j, k :: 0 <= j < i <= k < n ==> Array[j] <= Array[k]
    invariant forall j, k :: 0 <= j < k < i ==> Array[j] <= Array[k]
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i < j <= n
      invariant i <= minIndex < j
      invariant forall k :: i <= k < j ==> Array[minIndex] <= Array[k]
    {
      if Array[j] < Array[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      ghost var oldArray := Array[..];
      var temp := Array[i];
      Array[i] := Array[minIndex];
      Array[minIndex] := temp;
      SwapMultiset(oldArray, i, minIndex);
    }
    
    i := i + 1;
  }
}
// </vc-code>

