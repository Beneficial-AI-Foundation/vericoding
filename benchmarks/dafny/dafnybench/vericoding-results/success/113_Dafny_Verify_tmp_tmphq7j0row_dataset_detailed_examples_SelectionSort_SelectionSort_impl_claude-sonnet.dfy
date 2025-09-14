// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
lemma MinIndexCorrect(a: array<int>, start: int, minIndex: int)
  requires 0 <= start < a.Length
  requires start <= minIndex < a.Length
  requires forall k :: start <= k < a.Length ==> a[minIndex] <= a[k]
  ensures forall k :: start <= k < a.Length ==> a[minIndex] <= a[k]
{
}

lemma SwapPreservesMultiset(a: array<int>, i: int, j: int, oldContent: seq<int>)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  requires oldContent == a[..]
  ensures i == j ==> multiset(a[..]) == multiset(oldContent)
  ensures i != j && i < j ==> multiset(a[0..i] + [a[j]] + a[i+1..j] + [a[i]] + a[j+1..]) == multiset(oldContent)
  ensures i != j && j < i ==> multiset(a[0..j] + [a[i]] + a[j+1..i] + [a[j]] + a[i+1..]) == multiset(oldContent)
{
  if i == j {
    return;
  }
  if i < j {
    assert a[..] == a[0..i] + [a[i]] + a[i+1..j] + [a[j]] + a[j+1..];
    assert multiset(a[0..i] + [a[i]] + a[i+1..j] + [a[j]] + a[j+1..]) == multiset(a[0..i] + [a[j]] + a[i+1..j] + [a[i]] + a[j+1..]);
  } else {
    assert a[..] == a[0..j] + [a[j]] + a[j+1..i] + [a[i]] + a[i+1..];
    assert multiset(a[0..j] + [a[j]] + a[j+1..i] + [a[i]] + a[i+1..]) == multiset(a[0..j] + [a[i]] + a[j+1..i] + [a[j]] + a[i+1..]);
  }
}

lemma SortedPartitionPreserved(a: array<int>, sortedEnd: int)
  requires 0 <= sortedEnd < a.Length
  requires forall i,j :: 0 <= i < j < sortedEnd ==> a[i] <= a[j]
  requires forall k :: 0 <= k < sortedEnd ==> a[k] <= a[sortedEnd]
  ensures forall i,j :: 0 <= i < j <= sortedEnd ==> a[i] <= a[j]
{
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
  modifies a
  // Ensures the final array is sorted in ascending order
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // Ensures that the final array has the same elements as the initial array
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  if n <= 1 {
    return;
  }
  
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant forall x,y :: 0 <= x < y < i ==> a[x] <= a[y]
    invariant forall x :: 0 <= x < i ==> forall y :: i <= y < n ==> a[x] <= a[y]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i <= minIndex < n
      invariant i < j <= n
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      var oldContent := a[..];
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
      assert multiset(a[..]) == multiset(oldContent);
    }
    
    if i + 1 < n {
      SortedPartitionPreserved(a, i);
    }
    
    i := i + 1;
  }
}
// </vc-code>

