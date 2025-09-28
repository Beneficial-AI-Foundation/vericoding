// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
function min(a: int, b: int): int {
  if a < b then a else b
}

function max(a: int, b: int): int {
  if a > b then a else b
}

predicate IsPermutation(s1: seq<int>, s2: seq<int>)
{
  |s1| == |s2| && multiset(s1) == multiset(s2)
}

function swap(s: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < |s|
  requires 0 <= j < |s|
{
  s[i := s[j]][j := s[i]]
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop bounds and invariant in the inner loop to correctly identify the minimum element within the unsorted portion of the sequence. */
{
    var a := s;

    for i := 0 to |a|
      invariant 0 <= i <= |a|
      invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
      invariant forall k :: 0 <= k < i ==> (forall m :: i <= m < |a| ==> a[k] <= a[m])
      invariant IsPermutation(s, a)
    {
        if i == |a| { break; }
        var min_val := a[i];
        var min_idx := i;

        for j := i + 1 to |a|
          invariant i < j <= |a|
          invariant i <= min_idx < j
          invariant forall k :: i <= k < j ==> a[min_idx] <= a[k]
          invariant a[min_idx] == a[min_idx] // This invariant is trivially true, and serves to protect against issues when min_idx doesn't update.
          invariant IsPermutation(s, a)
        {
            if a[j] < a[min_idx] {
                min_val := a[j];
                min_idx := j;
            }
        }

        a := swap(a, i, min_idx);
    }
    sorted := a;
}
// </vc-code>
