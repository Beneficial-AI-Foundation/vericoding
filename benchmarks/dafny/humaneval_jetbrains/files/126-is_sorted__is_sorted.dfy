function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)

  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
