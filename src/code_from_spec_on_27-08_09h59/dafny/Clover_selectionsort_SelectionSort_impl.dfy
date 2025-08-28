// <vc-helpers>
lemma MultisetPreservation(a: array<int>, i: int, j: int, oldSeq: seq<int>)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j
  requires oldSeq == a[..]
  ensures multiset(a[..]) == multiset(oldSeq)
{
  var newSeq := a[..];
  assert multiset(oldSeq) == multiset(newSeq);
}

lemma SortedAfterMinPlacement(a: array<int>, sortedEnd: int, minIndex: int, oldA: seq<int>)
  requires 0 <= sortedEnd < a.Length
  requires sortedEnd <= minIndex < a.Length
  requires |oldA| == a.Length
  requires forall k :: sortedEnd <= k < a.Length ==> oldA[minIndex] <= oldA[k]
  requires forall i,j :: 0 <= i < j < sortedEnd ==> oldA[i] <= oldA[j]
  requires forall i :: 0 <= i < sortedEnd ==> forall j :: sortedEnd <= j < a.Length ==> oldA[i] <= oldA[j]
  requires a[..] == oldA[sortedEnd := oldA[minIndex]][minIndex := oldA[sortedEnd]]
  ensures forall i,j :: 0 <= i < j < sortedEnd + 1 ==> a[i] <= a[j]
  ensures forall i :: 0 <= i < sortedEnd + 1 ==> forall j :: sortedEnd + 1 <= j < a.Length ==> a[i] <= a[j]
{
  var swapped := oldA[sortedEnd := oldA[minIndex]][minIndex := oldA[sortedEnd]];
  assert a[..] == swapped;
  
  forall i, j | 0 <= i < j < sortedEnd + 1
    ensures a[i] <= a[j]
  {
    if i < sortedEnd && j < sortedEnd {
      assert oldA[i] <= oldA[j];
      if i != minIndex && j != minIndex {
        assert a[i] == oldA[i] && a[j] == oldA[j];
      } else if i == minIndex {
        assert a[i] == oldA[sortedEnd];
        assert a[j] == oldA[j];
        assert oldA[sortedEnd] <= oldA[j];
      } else if j == minIndex {
        assert a[i] == oldA[i];
        assert a[j] == oldA[sortedEnd];
        assert oldA[i] <= oldA[sortedEnd];
      }
    } else if i < sortedEnd && j == sortedEnd {
      assert a[j] == oldA[minIndex];
      if i != minIndex {
        assert a[i] == oldA[i];
        assert oldA[i] <= oldA[minIndex];
      } else {
        assert a[i] == oldA[sortedEnd];
        assert oldA[sortedEnd] <= oldA[minIndex];
      }
    }
  }
  
  forall i | 0 <= i < sortedEnd + 1
    ensures forall j :: sortedEnd + 1 <= j < a.Length ==> a[i] <= a[j]
  {
    forall j | sortedEnd + 1 <= j < a.Length
      ensures a[i] <= a[j]
    {
      if i < sortedEnd {
        if i != minIndex {
          assert a[i] == oldA[i];
          assert a[j] == oldA[j];
          assert oldA[i] <= oldA[j];
        } else {
          assert a[i] == oldA[sortedEnd];
          assert a[j] == oldA[j];
          assert oldA[sortedEnd] <= oldA[j];
        }
      } else {
        assert i == sortedEnd;
        assert a[i] == oldA[minIndex];
        assert a[j] == oldA[j];
        assert oldA[minIndex] <= oldA[j];
      }
    }
  }
}

lemma SwapPreservesMultiset(oldSeq: seq<int>, i: int, j: int)
  requires 0 <= i < |oldSeq|
  requires 0 <= j < |oldSeq|
  ensures multiset(oldSeq[i := oldSeq[j]][j := oldSeq[i]]) == multiset(oldSeq)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var n := a.Length;
  if n <= 1 {
    return;
  }
  
  var i := 0;
  ghost var originalSeq := a[..];
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant forall x,y :: 0 <= x < y < i ==> a[x] <= a[y]
    invariant forall x :: 0 <= x < i ==> forall y :: i <= y < n ==> a[x] <= a[y]
    invariant multiset(a[..]) == multiset(originalSeq)
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i < j <= n
      invariant i <= minIndex < j
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
      invariant multiset(a[..]) == multiset(originalSeq)
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      ghost var beforeSwap := a[..];
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
      SwapPreservesMultiset(beforeSwap, i, minIndex);
      assert multiset(a[..]) == multiset(beforeSwap);
      SortedAfterMinPlacement(a, i, minIndex, beforeSwap);
    }
    
    i := i + 1;
  }
}
// </vc-code>
