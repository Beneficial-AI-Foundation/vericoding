method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-helpers>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
  // pre-conditions-start
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  // pre-conditions-end
  // post-conditions-start
  ensures count == count_set(a, x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var c := 0;
  var i := pos;
  while i < |a| && a[i] == x
    invariant 0 <= pos <= i <= |a|
    invariant c == i - pos
    invariant forall k :: pos <= k < i ==> a[k] == x
    invariant (pos == 0 || (0 <= pos - 1 < |a| && a[pos - 1] < x))
    invariant forall k :: (0 <= k < pos) ==> a[k] < x
    invariant forall k :: (i <= k < |a|) ==> a[k] >= x // Added to ensure elements after i are >= x
  {
    c := c + 1;
    i := i + 1;
  }
  
  assert forall k | 0 <= k < pos :: a[k] < x;
  assert forall k | i <= k < |a| :: a[k] > x;

  assert (set k | 0 <= k < |a| && a[k] == x) == (set k | pos <= k < i);
  count := c;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end