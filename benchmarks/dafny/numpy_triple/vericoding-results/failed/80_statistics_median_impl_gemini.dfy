// <vc-preamble>
// Helper predicate to check if two sequences are permutations of each other
predicate IsPermutation(a: seq<real>, b: seq<real>)
{
  |a| == |b| &&
  (forall i :: 0 <= i < |a| ==> exists j :: 0 <= j < |b| && a[i] == b[j]) &&
  (forall j :: 0 <= j < |b| ==> exists i :: 0 <= i < |a| && b[j] == a[i])
}

// Helper predicate to check if a sequence is sorted in non-decreasing order
predicate IsSorted(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Method to compute the median of a non-empty sequence of real numbers
// </vc-preamble>

// <vc-helpers>
// Function to insert an element into a sorted sequence
function Insert(x: real, s: seq<real>): seq<real>
  requires IsSorted(s)
  ensures IsSorted(Insert(x, s))
  ensures multiset(Insert(x, s)) == multiset(s) + multiset{x}
  decreases |s|
{
  if s == [] then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}

// Function to sort a sequence using insertion sort
function Sort(a: seq<real>): seq<real>
  ensures IsSorted(Sort(a))
  ensures multiset(Sort(a)) == multiset(a)
  decreases |a|
{
  if a == [] then []
  else Insert(a[0], Sort(a[1..]))
}

// Lemma to connect multiset equality to the given IsPermutation predicate
lemma MultisetImpliesIsPermutation(a: seq<real>, b: seq<real>)
  requires multiset(a) == multiset(b)
  ensures IsPermutation(a, b)
{
  assert |a| == |b|;
  forall i | 0 <= i < |a|
    ensures exists j :: 0 <= j < |b| && a[i] == b[j]
  {
    var x := a[i];
    assert multiset(a)[x] > 0;
    assert multiset(b)[x] > 0;
    assert x in multiset(b);
    var j :| 0 <= j < |b| && b[j] == x;
  }
  forall j | 0 <= j < |b|
    ensures exists i :: 0 <= i < |a| && b[j] == a[i]
  {
    var y := b[j];
    assert multiset(b)[y] > 0;
    assert multiset(a)[y] > 0;
    assert y in multiset(a);
    var i :| 0 <= i < |a| && a[i] == y;
  }
}
// </vc-helpers>

// <vc-spec>
method median(a: seq<real>) returns (m: real)
  requires |a| >= 1
  ensures exists sorted: seq<real> ::
    // sorted is a permutation of the input sequence a
    IsPermutation(a, sorted) &&
    // sorted is in non-decreasing order
    IsSorted(sorted) &&
    // m is computed correctly based on whether the length is odd or even
    (if |sorted| % 2 == 1 then
      // odd case: middle element at index |sorted| / 2
      m == sorted[|sorted| / 2]
    else
      // even case: average of the two middle elements
      m == (sorted[|sorted| / 2 - 1] + sorted[|sorted| / 2]) / 2.0
    ) &&
    // median property: m is either an element from the sorted sequence,
    // or the average of two elements from the sorted sequence
    ((exists i :: 0 <= i < |sorted| && m == sorted[i]) ||
    (exists i, j :: (0 <= i < |sorted| && 0 <= j < |sorted| && 
                     m == (sorted[i] + sorted[j]) / 2.0)))
// </vc-spec>
// <vc-code>
{
  var sorted := Sort(a);
  MultisetImpliesIsPermutation(a, sorted);

  if |a| % 2 == 1 {
    m := sorted[|a| / 2];
  } else {
    m := (sorted[|a| / 2 - 1] + sorted[|a| / 2]) / 2.0;
  }
}
// </vc-code>
