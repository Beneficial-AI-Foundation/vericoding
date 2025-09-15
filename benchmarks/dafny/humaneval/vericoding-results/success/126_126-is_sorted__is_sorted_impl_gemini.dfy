// <vc-preamble>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-preamble>

// <vc-helpers>
lemma SortedAdjImpliesSorted(a: seq<int>)
  requires forall k :: 0 <= k < |a|-1 ==> a[k] <= a[k+1]
  ensures forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
{
  forall i, j | 0 <= i <= j < |a| ensures a[i] <= a[j] {
    var k := i;
    while k < j
      invariant i <= k <= j
      invariant a[i] <= a[k]
      decreases j - k
    {
      k := k + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)

  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
// </vc-spec>
// <vc-code>
{
  var sorted_by_adj := forall k :: 0 <= k < |a|-1 ==> a[k] <= a[k+1];
  var counts_ok := forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2;
  f := sorted_by_adj && counts_ok;
  if f {
    SortedAdjImpliesSorted(a);
  }
}
// </vc-code>
