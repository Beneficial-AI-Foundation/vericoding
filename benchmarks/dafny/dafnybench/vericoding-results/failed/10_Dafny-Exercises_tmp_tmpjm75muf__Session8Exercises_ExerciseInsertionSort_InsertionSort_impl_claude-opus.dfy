predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma SortedSegExtend(a: array<int>, i: int, j: int)
  requires 0 <= i <= j < a.Length
  requires sorted_seg(a, i, j)
  requires j + 1 < a.Length
  requires forall k :: i <= k <= j ==> a[k] <= a[j+1]
  ensures sorted_seg(a, i, j+1)
{
  forall l, k | i <= l <= k <= j+1
    ensures a[l] <= a[k]
  {
    if k == j+1 {
      assert i <= l <= j;
      assert a[l] <= a[j+1];
    } else {
      assert i <= l <= k <= j;
      assert a[l] <= a[k];
    }
  }
}

lemma SortedSegMerge(a: array<int>, i: int, m: int, j: int)
  requires 0 <= i <= m < j <= a.Length - 1
  requires sorted_seg(a, i, m)
  requires sorted_seg(a, m+1, j)
  requires a[m] <= a[m+1]
  ensures sorted_seg(a, i, j)
{
  forall l, k | i <= l <= k <= j
    ensures a[l] <= a[k]
  {
    if l <= m && k <= m {
      assert a[l] <= a[k];
    } else if m+1 <= l && m+1 <= k {
      assert a[l] <= a[k];
    } else if l <= m && m+1 <= k {
      assert a[l] <= a[m];
      assert a[m] <= a[m+1];
      assert a[m+1] <= a[k];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
// </vc-spec>
// <vc-code>
{
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var key := a[i];
    var j := i - 1;
    
    ghost var a_before := a[..];
    
    while j >= 0 && a[j] > key
      invariant -1 <= j <= i - 1
      invariant a[..] == a_before[..j+1] + [if j == i-1 then key else a_before[j+1]] + a_before[j+2..i+1] + a_before[i+1..]
      invariant sorted_seg(a, 0, j)
      invariant j+2 <= i ==> sorted_seg(a, j+2, i)
      invariant j >= 0 ==> forall k :: j+2 <= k <= i ==> a[j] < a[k]
      invariant forall k, l :: 0 <= k <= j && j+2 <= l <= i ==> a[k] <= a[l]
      invariant multiset(a[..]) == multiset(a_before)
    {
      a[j+1] := a[j];
      j := j - 1;
    }
    
    a[j+1] := key;
    
    assert sorted_seg(a, 0, j);
    
    if j >= 0 {
      assert a[j] <= a[j+1];
      forall l, k | 0 <= l <= k <= j+1
        ensures a[l] <= a[k]
      {
        if k == j+1 {
          if l <= j {
            assert a[l] <= a[j];
            assert a[j] <= a[j+1];
          }
        } else {
          assert sorted_seg(a, 0, j);
        }
      }
      assert sorted_seg(a, 0, j+1);
    } else {
      assert j == -1;
      assert sorted_seg(a, 0, 0);
    }
    
    if j+2 <= i {
      assert sorted_seg(a, j+2, i);
      assert a[j+1] < a[j+2];
      forall l, k | j+1 <= l <= k <= i
        ensures a[l] <= a[k]
      {
        if l == j+1 {
          if k == j+1 {
            assert a[l] <= a[k];
          } else {
            assert k >= j+2;
            assert a[j+1] < a[j+2];
            assert sorted_seg(a, j+2, i);
            assert a[j+2] <= a[k];
          }
        } else {
          assert l >= j+2;
          assert sorted_seg(a, j+2, i);
        }
      }
      assert sorted_seg(a, j+1, i);
      
      if j >= 0 {
        SortedSegMerge(a, 0, j+1, i);
      }
    }
    
    assert sorted_seg(a, 0, i);
    
    i := i + 1;
  }
}
// </vc-code>

