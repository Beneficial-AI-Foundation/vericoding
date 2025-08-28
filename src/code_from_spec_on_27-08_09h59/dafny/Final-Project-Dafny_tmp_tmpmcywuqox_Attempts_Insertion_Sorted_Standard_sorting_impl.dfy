predicate InsertionSorted(Array: array<int>, left: int, right: int)  
  requires 0 <= left <= right <= Array.Length       
  reads Array       
{           
  forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}

// <vc-helpers>
lemma SortedPreservation(Array: array<int>, left: int, right: int, i: int, j: int)
  requires 0 <= left <= i < j <= right <= Array.Length
  requires InsertionSorted(Array, left, i)
  requires InsertionSorted(Array, j, right)
  requires forall k :: left <= k < i ==> Array[k] <= Array[i]
  requires forall k :: j < k < right ==> Array[i] <= Array[k]
  ensures InsertionSorted(Array, left, right)
{}

lemma InsertIntoSorted(Array: array<int>, left: int, right: int, pos: int)
  requires 0 <= left <= pos < right <= Array.Length
  requires InsertionSorted(Array, left, pos)
  requires InsertionSorted(Array, pos + 1, right)
  requires forall k :: left <= k < pos ==> Array[k] <= Array[pos]
  requires forall k :: pos < k < right ==> Array[pos] <= Array[k]
  ensures InsertionSorted(Array, left, right)
{}

lemma InsertionPreservesOrder(Array: array<int>, pos: int, key: int, left: int, right: int)
  requires 0 <= left <= pos < right <= Array.Length
  requires InsertionSorted(Array, left, pos)
  requires forall k :: left <= k <= pos ==> Array[k] <= key
  requires Array[pos] == key
  ensures InsertionSorted(Array, left, pos + 1)
{}

lemma InsertionSortAfterInsert(Array: array<int>, j: int, key: int, i: int)
  requires 0 <= j + 1 <= i < Array.Length
  requires InsertionSorted(Array, 0, j + 1)
  requires forall k :: j + 1 < k <= i ==> Array[k] >= key
  requires Array[j + 1] == key
  requires forall k :: 0 <= k <= j ==> Array[k] <= key
  ensures InsertionSorted(Array, 0, i + 1)
{
  forall a, b | 0 <= a < b < i + 1
    ensures Array[a] <= Array[b]
  {
    if b <= j {
      assert InsertionSorted(Array, 0, j + 1);
      assert Array[a] <= Array[b];
    } else if a <= j && b == j + 1 {
      assert Array[a] <= key;
      assert Array[b] == key;
      assert Array[a] <= Array[b];
    } else if a <= j && b > j + 1 {
      assert Array[a] <= key;
      assert Array[b] >= key;
      assert Array[a] <= Array[b];
    } else if a == j + 1 && b > j + 1 {
      assert Array[a] == key;
      assert Array[b] >= key;
      assert Array[a] <= Array[b];
    } else {
      assert j + 1 < a < b <= i;
      assert Array[a] >= key;
      assert Array[b] >= key;
      assert Array[a] <= Array[b];
    }
  }
}

lemma EmptyRangeSorted(Array: array<int>, left: int, right: int)
  requires 0 <= left <= right <= Array.Length
  requires left >= right
  ensures InsertionSorted(Array, left, right)
{}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method sorting(Array: array<int>)
  requires Array.Length > 1 
  ensures InsertionSorted(Array, 0, Array.Length) 
  modifies Array
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if Array.Length <= 1 {
    return;
  }
  
  var i := 1;
  
  while i < Array.Length
    invariant 1 <= i <= Array.Length
    invariant InsertionSorted(Array, 0, i)
  {
    var key := Array[i];
    var j := i - 1;
    
    ghost var oldArray := Array[..];
    
    while j >= 0 && Array[j] > key
      invariant -1 <= j < i
      invariant InsertionSorted(Array, 0, j + 1)
      invariant forall k :: j + 1 < k <= i ==> Array[k] >= key
      invariant forall k :: j + 1 < k <= i ==> Array[k] == oldArray[k - 1]
      invariant key == oldArray[i]
      invariant forall k :: 0 <= k <= j ==> Array[k] == oldArray[k]
      invariant forall k :: i < k < Array.Length ==> Array[k] == oldArray[k]
      decreases j
    {
      Array[j + 1] := Array[j];
      j := j - 1;
    }
    
    Array[j + 1] := key;
    
    assert forall k :: 0 <= k <= j ==> Array[k] <= key;
    assert forall k :: j + 1 < k <= i ==> Array[k] >= key;
    assert Array[j + 1] == key;
    
    InsertionSortAfterInsert(Array, j, key, i);
    
    i := i + 1;
  }
}
// </vc-code>
