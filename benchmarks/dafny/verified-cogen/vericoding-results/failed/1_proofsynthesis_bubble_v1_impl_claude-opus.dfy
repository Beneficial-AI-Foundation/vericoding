// <vc-preamble>
predicate SortedBetween(a: seq<int>, from: int, to: int)
    requires 0 <= from <= to <= |a|
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

predicate IsReorderOf<T(==)>(r: seq<int>, p: seq<T>, s: seq<T>)
    requires |r| == |p| && |r| == |s|
{
    && |r| == |s|
    && (forall i :: 0 <= i < |r| ==> 0 <= r[i] < |s|)
    && (forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j])
    && (forall i :: 0 <= i < |r| ==> p[i] == s[r[i]])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix filter multiset postcondition and partition lemma */
function Partition(a: seq<int>, pivot: int): (seq<int>, seq<int>, seq<int>)
  ensures var (less, equal, greater) := Partition(a, pivot);
          |less| <= |a| && |equal| <= |a| && |greater| <= |a| &&
          |less| + |equal| + |greater| == |a| &&
          (forall x :: x in less ==> x < pivot) &&
          (forall x :: x in equal ==> x == pivot) &&
          (forall x :: x in greater ==> x > pivot) &&
          multiset(less + equal + greater) == multiset(a)
{
  var less := filter(x => x < pivot, a);
  var equal := filter(x => x == pivot, a);
  var greater := filter(x => x > pivot, a);
  FilterPartitionLemma(a, pivot, less, equal, greater);
  (less, equal, greater)
}

function filter<T>(f: T -> bool, s: seq<T>): seq<T>
  ensures |filter(f, s)| <= |s|
  ensures multiset(filter(f, s)) <= multiset(s)
  ensures forall x :: x in filter(f, s) ==> x in s && f(x)
  decreases |s|
{
  if |s| == 0 then []
  else if f(s[0]) then
    var rest := filter(f, s[1..]);
    assert multiset(s[1..]) <= multiset(s);
    assert multiset(rest) <= multiset(s[1..]);
    [s[0]] + rest
  else 
    var rest := filter(f, s[1..]);
    assert multiset(s[1..]) <= multiset(s);
    assert multiset(rest) <= multiset(s[1..]);
    rest
}

lemma FilterPartitionLemma(a: seq<int>, pivot: int, less: seq<int>, equal: seq<int>, greater: seq<int>)
  requires less == filter(x => x < pivot, a)
  requires equal == filter(x => x == pivot, a)
  requires greater == filter(x => x > pivot, a)
  ensures |less| + |equal| + |greater| == |a|
  ensures multiset(less + equal + greater) == multiset(a)
  decreases |a|
{
  if |a| == 0 {
    assert less == [] && equal == [] && greater == [];
  } else {
    var rest_less := filter(x => x < pivot, a[1..]);
    var rest_equal := filter(x => x == pivot, a[1..]);
    var rest_greater := filter(x => x > pivot, a[1..]);
    FilterPartitionLemma(a[1..], pivot, rest_less, rest_equal, rest_greater);
    
    if a[0] < pivot {
      assert less == [a[0]] + rest_less;
      assert equal == rest_equal;
      assert greater == rest_greater;
      assert multiset(less + equal + greater) == multiset{a[0]} + multiset(rest_less + rest_equal + rest_greater);
      assert multiset{a[0]} + multiset(a[1..]) == multiset(a);
    } else if a[0] == pivot {
      assert less == rest_less;
      assert equal == [a[0]] + rest_equal;
      assert greater == rest_greater;
      assert multiset(less + equal + greater) == multiset{a[0]} + multiset(rest_less + rest_equal + rest_greater);
      assert multiset{a[0]} + multiset(a[1..]) == multiset(a);
    } else {
      assert less == rest_less;
      assert equal == rest_equal;
      assert greater == [a[0]] + rest_greater;
      assert multiset(less + equal + greater) == multiset{a[0]} + multiset(rest_less + rest_equal + rest_greater);
      assert multiset{a[0]} + multiset(a[1..]) == multiset(a);
    }
  }
}

function QuickSort(a: seq<int>): seq<int>
  ensures |QuickSort(a)| == |a|
  ensures multiset(QuickSort(a)) == multiset(a)
  ensures SortedBetween(QuickSort(a), 0, |QuickSort(a)|)
  decreases |a|
{
  if |a| <= 1 then a
  else
    var pivot := a[|a|/2];
    var (less, equal, greater) := Partition(a, pivot);
    assert |less| < |a| && |greater| < |a| by {
      PartitionSmallerThanOriginal(a, pivot);
    }
    var sortedLess := QuickSort(less);
    var sortedGreater := QuickSort(greater);
    var lessFiltered := filter(x => x < pivot, a);
    assert less == lessFiltered;
    assert forall x :: x in less ==> x < pivot;
    QuickSortCombineLemma(sortedLess, equal, sortedGreater, pivot);
    sortedLess + equal + sortedGreater
}

lemma PartitionSmallerThanOriginal(a: seq<int>, pivot: int)
  requires |a| > 1 && pivot == a[|a|/2]
  ensures var (less, equal, greater) := Partition(a, pivot);
          |less| < |a| && |greater| < |a| && |equal| >= 1
{
  var (less, equal, greater) := Partition(a, pivot);
  assert pivot in a;
  assert pivot in equal by {
    assert a[|a|/2] == pivot;
    assert filter(x => x == pivot, a) == equal;
  }
  assert |equal| >= 1;
}

lemma QuickSortCombineLemma(less: seq<int>, equal: seq<int>, greater: seq<int>, pivot: int)
  requires SortedBetween(less, 0, |less|)
  requires SortedBetween(greater, 0, |greater|)
  requires forall x :: x in less ==> x < pivot
  requires forall x :: x in equal ==> x == pivot
  requires forall x :: x in greater ==> x > pivot
  ensures SortedBetween(less + equal + greater, 0, |less + equal + greater|)
{
  var combined := less + equal + greater;
  forall i, j | 0 <= i < j < |combined|
    ensures combined[i] <= combined[j]
  {
    if i < |less| && j < |less| {
      assert combined[i] == less[i] && combined[j] == less[j];
    } else if i < |less| && j < |less| + |equal| {
      assert combined[i] in less;
      assert combined[j] in equal;
    } else if i < |less| && j >= |less| + |equal| {
      assert combined[i] in less;
      assert combined[j] in greater;
    } else if i < |less| + |equal| && j < |less| + |equal| {
      assert combined[i] in equal;
      assert combined[j] in equal;
    } else if i < |less| + |equal| && j >= |less| + |equal| {
      assert combined[i] in equal;
      assert combined[j] in greater;
    } else {
      assert i >= |less| + |equal| && j >= |less| + |equal|;
      var gi := i - |less| - |equal|;
      var gj := j - |less| - |equal|;
      assert 0 <= gi < gj < |greater|;
      assert combined[i] == greater[gi] && combined[j] == greater[gj];
    }
  }
}

function BuildReorder(a: seq<int>, sorted: seq<int>): seq<int>
  requires |a| == |sorted|
  requires multiset(a) == multiset(sorted)
  ensures |BuildReorder(a, sorted)| == |a|
  ensures IsReorderOf(BuildReorder(a, sorted), sorted, a)
  decreases |a|
{
  if |a| == 0 then []
  else
    assert sorted[0] in multiset(sorted);
    assert sorted[0] in multiset(a);
    assert sorted[0] in a;
    var idx := FindIndex(a, sorted[0]);
    assert multiset(RemoveAt(a, idx)) == multiset(a) - multiset{a[idx]} by {
      RemoveAtPreservesMultiset(a, idx);
    }
    assert sorted[0] == a[idx];
    assert multiset(sorted[1..]) == multiset(sorted) - multiset{sorted[0]} by {
      assert sorted == [sorted[0]] + sorted[1..];
      assert multiset(sorted) == multiset{sorted[0]} + multiset(sorted[1..]);
    }
    assert multiset(RemoveAt(a, idx)) == multiset(sorted[1..]);
    [idx] + MapIndices(BuildReorder(RemoveAt(a, idx), sorted[1..]), idx)
}

function MapIndices(r: seq<int>, removed: int): seq<int>
  ensures |MapIndices(r, removed)| == |r|
  ensures forall i :: 0 <= i < |r| ==> 
    MapIndices(r, removed)[i] == if r[i] < removed then r[i] else r[i] + 1
{
  if |r| == 0 then []
  else [if r[0] < removed then r[0] else r[0] + 1] + MapIndices(r[1..], removed)
}

function FindIndex(s: seq<int>, x: int): int
  requires x in s
  ensures 0 <= FindIndex(s, x) < |s|
  ensures s[FindIndex(s, x)] == x
{
  if s[0] == x then 0
  else 1 + FindIndex(s[1..], x)
}

function RemoveAt<T>(s: seq<T>, idx: int): seq<T>
  requires 0 <= idx < |s|
  ensures |RemoveAt(s, idx)| == |s| - 1
  ensures forall i :: 0 <= i < idx ==> RemoveAt(s, idx)[i] == s[i]
  ensures forall i :: idx <= i < |s| - 1 ==> RemoveAt(s, idx)[i] == s[i + 1]
  ensures RemoveAt(s, idx) == s[..idx] + s[idx+1..]
{
  s[..idx] + s[idx+1..]
}

lemma RemoveAtPreservesMultiset<T>(s: seq<T>, idx: int)
  requires 0 <= idx < |s|
  ensures multiset(RemoveAt(s, idx)) == multiset(s) - multiset{s[idx]}
{
  var removed := RemoveAt(s, idx);
  assert removed == s[..idx] + s[idx+1..];
  calc == {
    multiset(removed);
    multiset(s[..idx] + s[idx+1..]);
    multiset(s[..idx]) + multiset(s[idx+1..]);
    { assert s == s[..idx] + [s[idx]] + s[idx+1..]; }
    multiset(s) - multiset{s[idx]};
  }
}
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: |r| == nums.Length && IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use QuickSort with correct array operations */
{
  if nums.Length == 0 {
    return;
  }
  
  var sorted := QuickSort(nums[..]);
  assert SortedBetween(sorted, 0, |sorted|);
  assert multiset(sorted) == multiset(nums[..]);
  
  var oldNums := nums[..];
  var r := BuildReorder(oldNums, sorted);
  
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant nums[..i] == sorted[..i]
    invariant nums[i..] == oldNums[i..]
    invariant SortedBetween(sorted[..i], 0, i)
  {
    nums[i] := sorted[i];
    i := i + 1;
  }
  
  assert nums[..] == sorted;
  assert SortedBetween(nums[..], 0, nums.Length);
  assert |r| == nums.Length;
  assert IsReorderOf(r, nums[..], old(nums[..]));
}
// </vc-code>
