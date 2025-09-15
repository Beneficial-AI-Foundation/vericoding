// <vc-preamble>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-preamble>

// <vc-helpers>
predicate IsNondecreasing(a: seq<int>) {
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

predicate CountAtMostTwoPerValue(a: seq<int>) {
  forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
}

function ValidSortedWithBound(a: seq<int>): bool {
  IsNondecreasing(a) && CountAtMostTwoPerValue(a)
}
// </vc-helpers>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)

  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
// </vc-spec>
// <vc-code>
{
  var sorted := forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j];
  var bounded := forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2;
  f := sorted && bounded;
}
// </vc-code>
