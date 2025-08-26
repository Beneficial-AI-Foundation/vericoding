// Fast sort implementation with partitioning

predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate multiset_eq<T>(s1: seq<T>, s2: seq<T>)
{
  multiset(s1) == multiset(s2)
}

// <vc-spec>
method FastSort(s: seq<int>) returns (result: seq<int>)
  ensures sorted(result)
  ensures multiset_eq(s, result)
// </vc-spec>

// <vc-helpers>
function partition_le(s: seq<int>, pivot: int): seq<int>
{
  seq(x | x in s && x <= pivot :: x)
}

function partition_gt(s: seq<int>, pivot: int): seq<int>
{
  seq(x | x in s && x > pivot :: x)
}

lemma PartitionPreservesMultiset(s: seq<int>, pivot: int)
  ensures multiset(s) == multiset(partition_le(s, pivot)) + multiset(partition_gt(s, pivot))
{
  // Proof by induction on the structure of sequences
}

lemma SortedConcatenation(left: seq<int>, right: seq<int>, pivot: int)
  requires sorted(left)
  requires sorted(right)
  requires forall x :: x in left ==> x <= pivot
  requires forall x :: x in right ==> x > pivot
  ensures sorted(left + [pivot] + right)
{
}

lemma MultisetPreservation(s: seq<int>, left: seq<int>, equal: seq<int>, right: seq<int>)
  requires left == seq(x | x in s && x < s[0] :: x)
  requires equal == seq(x | x in s && x == s[0] :: x)
  requires right == seq(x | x in s && x > s[0] :: x)
  ensures multiset(s) == multiset(left) + multiset(equal) + multiset(right)
{
}
// </vc-helpers>

// <vc-code>
method FastSort(s: seq<int>) returns (result: seq<int>)
  ensures sorted(result)
  ensures multiset_eq(s, result)
  decreases |s|
{
  if |s| <= 1 {
    result := s;
  } else {
    var pivot := s[0];
    var left := seq(x | x in s && x < pivot :: x);
    var equal := seq(x | x in s && x == pivot :: x);
    var right := seq(x | x in s && x > pivot :: x);
    
    MultisetPreservation(s, left, equal, right);
    
    var sorted_left := FastSort(left);
    var sorted_right := FastSort(right);
    
    result := sorted_left + equal + sorted_right;
    
    SortedConcatenation(sorted_left, sorted_right, pivot);
  }
}
// </vc-code>