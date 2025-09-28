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
/* helper modified by LLM (iteration 5): Simplified SortSeq with proper permutation logic */
function SortSeq(a: seq<real>): seq<real>
  ensures |SortSeq(a)| == |a|
  ensures IsPermutation(a, SortSeq(a))
  ensures IsSorted(SortSeq(a))
  decreases |a|
{
  if |a| <= 1 then 
    a
  else
    var pivot := a[0];
    var rest := a[1..];
    var less := FilterLess(rest, pivot);
    var geq := FilterGeq(rest, pivot);
    SortSeq(less) + [pivot] + SortSeq(geq)
}

function FilterLess(s: seq<real>, pivot: real): seq<real>
  ensures forall x :: x in FilterLess(s, pivot) ==> x in s && x < pivot
  ensures |FilterLess(s, pivot)| <= |s|
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] < pivot then [s[0]] + FilterLess(s[1..], pivot)
  else FilterLess(s[1..], pivot)
}

function FilterGeq(s: seq<real>, pivot: real): seq<real>
  ensures forall x :: x in FilterGeq(s, pivot) ==> x in s && x >= pivot
  ensures |FilterGeq(s, pivot)| <= |s|
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] >= pivot then [s[0]] + FilterGeq(s[1..], pivot)
  else FilterGeq(s[1..], pivot)
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
/* code modified by LLM (iteration 5): Using SortSeq to compute median */
{
  var sorted := SortSeq(a);
  
  if |sorted| % 2 == 1 {
    m := sorted[|sorted| / 2];
  } else {
    m := (sorted[|sorted| / 2 - 1] + sorted[|sorted| / 2]) / 2.0;
  }
}
// </vc-code>
