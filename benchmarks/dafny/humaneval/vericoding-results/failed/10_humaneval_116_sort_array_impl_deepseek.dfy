// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sequence slicing bounds and added lemma for bubble sort */
function popcount_compare(a: nat, b: nat): bool { popcount(a) <= popcount(b) }
lemma permutation_multiset_swap(arr: seq<nat>, i: int, j: int)
  requires 0 <= i < j < |arr|
  ensures multiset(arr[..i] + [arr[j]] + arr[i+1..j] + [arr[i]] + arr[j+1..]) == multiset(arr)
{
  // This is true by multiset properties
}
lemma bubble_sort_preserves_multiset(arr: seq<nat>, i: int, j: int)
  requires 0 <= i < j < |arr|
  ensures multiset(arr[..i] + [arr[j]] + arr[i+1..j] + [arr[i]] + arr[j+1..]) == multiset(arr)
{
  permutation_multiset_swap(arr, i, j);
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed bubble sort with proper bounds checking and swapping */
  sorted := s;
  var i := 0;
  while i < |sorted|
    decreases |sorted| - i
  {
    var j := 0;
    while j < |sorted| - i - 1
      decreases |sorted| - i - j - 1
    {
      if popcount(sorted[j]) > popcount(sorted[j+1]) {
        // Swap elements at j and j+1
        sorted := sorted[..j] + [sorted[j+1]] + sorted[j..j+1] + sorted[j+2..];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
