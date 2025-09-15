// <vc-preamble>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)

  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x

  ensures count == count_set(a, x)
// </vc-spec>
// <vc-code>
{
  var last := pos;
  while last + 1 < |a| && a[last + 1] == x
  {
    last := last + 1;
  }
  count := last - pos + 1;
}
// </vc-code>
