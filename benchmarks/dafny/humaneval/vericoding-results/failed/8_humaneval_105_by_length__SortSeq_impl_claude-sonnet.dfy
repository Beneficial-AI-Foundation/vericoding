// <vc-preamble>
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma for multiset preservation during swaps */
predicate IsSorted(arr: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |arr|
{
  forall i, j :: start <= i < j < end ==> arr[i] <= arr[j]
}

lemma SwapMaintainsMultiset(arr: seq<int>, i: int, j: int)
  requires 0 <= i < |arr| && 0 <= j < |arr|
  ensures multiset(arr) == multiset(arr[i := arr[j]][j := arr[i]])
{
}

lemma SwapSortedRange(arr: seq<int>, i: int, j: int, start: int, end: int)
  requires 0 <= i < |arr| && 0 <= j < |arr|
  requires 0 <= start <= end <= |arr|
  requires (i < start || i >= end) && (j < start || j >= end)
  requires forall x, y :: start <= x < y < end ==> arr[x] <= arr[y]
  ensures forall x, y :: start <= x < y < end ==> arr[i := arr[j]][j := arr[i]][x] <= arr[i := arr[j]][j := arr[i]][y]
{
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simplified loop invariants to fix verification */
  sorted := s;
  if |sorted| <= 1 {
    return;
  }
  
  var i := 1;
  while i < |sorted|
    invariant 1 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant |sorted| == |s|
      invariant multiset(s) == multiset(sorted)
      invariant forall x, y :: 0 <= x < y < j ==> sorted[x] <= sorted[y]
      invariant forall x, y :: j+1 <= x < y < i+1 ==> sorted[x] <= sorted[y]
      invariant j < i ==> forall k :: j < k <= i ==> sorted[j] <= sorted[k]
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
