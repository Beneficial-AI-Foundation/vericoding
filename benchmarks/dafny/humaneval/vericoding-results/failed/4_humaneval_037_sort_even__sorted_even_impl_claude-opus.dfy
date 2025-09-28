// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed precondition issues and termination, simplified multiset lemma */
function extract_even(a: seq<int>, i: nat): seq<int>
  requires i <= |a|
  ensures |extract_even(a, i)| <= |a| - i
  decreases |a| - i
{
  if i >= |a| then []
  else if i % 2 == 0 then 
    [a[i]] + extract_even(a, i + 2)
  else 
    extract_even(a, i + 1)
}

function merge_sorted(sorted_evens: seq<int>, original: seq<int>): seq<int>
  requires |sorted_evens| == (|original| + 1) / 2
  ensures |merge_sorted(sorted_evens, original)| == |original|
  ensures forall i :: 0 <= i < |original| && i % 2 == 1 ==> merge_sorted(sorted_evens, original)[i] == original[i]
  ensures forall i :: 0 <= i < |sorted_evens| ==> 2 * i < |original| ==> merge_sorted(sorted_evens, original)[2 * i] == sorted_evens[i]
{
  merge_sorted_helper(sorted_evens, original, 0)
}

function merge_sorted_helper(sorted_evens: seq<int>, original: seq<int>, i: nat): seq<int>
  requires |sorted_evens| == (|original| + 1) / 2
  requires i <= |original|
  ensures |merge_sorted_helper(sorted_evens, original, i)| == |original| - i
  ensures forall k :: 0 <= k < |original| - i && (i + k) % 2 == 1 ==> merge_sorted_helper(sorted_evens, original, i)[k] == original[i + k]
  ensures forall k :: 0 <= k < |original| - i && (i + k) % 2 == 0 ==> (i + k) / 2 < |sorted_evens| ==> merge_sorted_helper(sorted_evens, original, i)[k] == sorted_evens[(i + k) / 2]
  decreases |original| - i
{
  if i >= |original| then []
  else if i % 2 == 0 then 
    [sorted_evens[i / 2]] + merge_sorted_helper(sorted_evens, original, i + 1)
  else 
    [original[i]] + merge_sorted_helper(sorted_evens, original, i + 1)
}

lemma ExtractEvenSize(a: seq<int>, i: nat)
  requires i <= |a|
  ensures |extract_even(a, i)| == ((|a| - i + 1) / 2)
  decreases |a| - i
{
  if i >= |a| {
    assert |extract_even(a, i)| == 0;
    assert ((|a| - i + 1) / 2) == 0;
  } else if i % 2 == 0 {
    if i + 2 <= |a| {
      ExtractEvenSize(a, i + 2);
    }
  } else {
    if i + 1 <= |a| {
      ExtractEvenSize(a, i + 1);
    }
  }
}

lemma MergeSortedMultiset(sorted_evens: seq<int>, original: seq<int>)
  requires |sorted_evens| == (|original| + 1) / 2
  requires multiset(sorted_evens) == multiset(extract_even(original, 0))
  ensures multiset(merge_sorted(sorted_evens, original)) == multiset(original)
{
  var i := 0;
  var result := merge_sorted_helper(sorted_evens, original, 0);
  assert result == merge_sorted(sorted_evens, original);
}

method sort_seq(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures multiset(sorted) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  if |s| == 0 {
    return [];
  }
  var i := 0;
  sorted := s;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall k, l :: 0 <= k < l < i ==> sorted[k] <= sorted[l]
    invariant forall k :: 0 <= k < i ==> forall l :: i <= l < |sorted| ==> sorted[k] <= sorted[l]
  {
    var j := i;
    var minIdx := i;
    while j < |sorted|
      invariant i <= j <= |sorted|
      invariant i <= minIdx < |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIdx] <= sorted[k]
    {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIdx]][minIdx := temp];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)

  requires |a| > 0

  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Call helper lemmas for verification */
{
  var evens := extract_even(a, 0);
  ExtractEvenSize(a, 0);
  assert |evens| == (|a| + 1) / 2;
  
  var sorted_evens := sort_seq(evens);
  assert multiset(sorted_evens) == multiset(evens);
  assert multiset(sorted_evens) == multiset(extract_even(a, 0));
  
  sorted := merge_sorted(sorted_evens, a);
  MergeSortedMultiset(sorted_evens, a);
  
  assert |sorted| == |a|;
  assert forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i];
  assert multiset(sorted) == multiset(a);
}
// </vc-code>
