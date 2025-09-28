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
/* helper modified by LLM (iteration 5): Rewritten using selection sort with simplified invariants for better verification */
method Sort(a: seq<real>) returns (sorted: seq<real>)
  requires |a| >= 1
  ensures IsPermutation(a, sorted)
  ensures IsSorted(sorted)
{
  var n := |a|;
  var arr := new real[n];
  for i := 0 to n - 1
  {
    arr[i] := a[i];
  }
  ghost var ms := multiset(a);
  assert multiset(arr[..]) == ms;
  for i := 0 to n - 2
    invariant 0 <= i < n
    invariant IsSorted(arr[..i])
    invariant multiset(arr[..]) == ms
    invariant forall k, l :: 0 <= k < i <= l < n ==> arr[k] <= arr[l]
  {
    var minIdx := i;
    for j := i + 1 to n - 1
      invariant i <= minIdx < n
      invariant i <= j <= n
      invariant forall k :: i <= k < j ==> arr[k] >= arr[minIdx]
    {
      if arr[j] < arr[minIdx]
      {
        minIdx := j;
      }
    }
    var temp := arr[i];
    arr[i] := arr[minIdx];
    arr[minIdx] := temp;
  }
  sorted := [];
  for i := 0 to n - 1
  {
    sorted := sorted + [arr[i]];
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
/* code modified by LLM (iteration 5): Implementation remains unchanged as the helper fixes should resolve verification */
{
  var sorted := Sort(a);
  if |sorted| % 2 == 1
  {
    m := sorted[|sorted| / 2];
  }
  else
  {
    m := (sorted[|sorted| / 2 - 1] + sorted[|sorted| / 2]) / 2.0;
  }
}
// </vc-code>
