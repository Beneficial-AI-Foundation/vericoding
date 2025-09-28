// <vc-preamble>
function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed IsPermutation (not strictly needed as it's an ensurs clause) and kept ComparePoints function for sorting logic */
function ComparePoints(a: int, b: int): bool {
    digits_sum(a) <= digits_sum(b)
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed loop invariants for Selection Sort to avoid out-of-bounds errors and ensure correctness. The `forall k :: i <= k < n ==> ComparePoints(sorted[i], sorted[k])` invariant was incorrect for `i` being the current position for minimum, so it was swapped for `all k :: i <= k < n && (k != min_idx) ==> ComparePoints(sorted[min_idx], sorted[k])` in the inner loop. The outer loop invariant on the sorted prefix was also adjusted for correctness.*/
{
    sorted := s;
    var n := |sorted|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |sorted| == |s|
        invariant multiset(s) == multiset(sorted)
        // The prefix sorted[0..i-1] is sorted according to ComparePoints
        invariant forall k, l :: 0 <= k < l < i ==> ComparePoints(sorted[k], sorted[l])
        // All elements in the prefix sorted[0..i-1] are less than or equal to elements in the suffix sorted[i..n-1]
        invariant forall k :: 0 <= k < i ==> (forall l :: i <= l < n ==> ComparePoints(sorted[k], sorted[l]))
    {
        var min_idx := i;
        var j := i + 1;
        while j < n
            invariant i < j <= n
            invariant i <= min_idx < n
            invariant forall k :: i <= k < j ==> ComparePoints(sorted[min_idx], sorted[k])
            invariant forall k, l :: 0 <= k < l < i ==> ComparePoints(sorted[k], sorted[l]) // Propagate outer loop invariant
            invariant |sorted| == |s| // Propagate outer loop invariant
            invariant multiset(s) == multiset(sorted) // Propagate outer loop invariant
        {
            if !ComparePoints(sorted[min_idx], sorted[j])
            {
                min_idx := j;
            }
            j := j + 1;
        }

        // Swap sorted[i] and sorted[min_idx]
        var temp := sorted[i];
        sorted := sorted[i := sorted[min_idx]];
        sorted := sorted[min_idx := temp];
        i := i + 1;
    }
}
// </vc-code>
