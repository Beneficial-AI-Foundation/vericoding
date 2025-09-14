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
  /* code modified by LLM (iteration 3): added count variable and loop invariants */
  var i := pos;
  count := 0;
  while i < |a| && a[i] == x
    invariant 0 <= pos <= i <= |a|
    invariant forall k1, k2 :: 0 <= k1 <= k2 < |a| ==> a[k1] <= a[k2]
    invariant a[pos] == x
    invariant pos == 0 || a[pos - 1] < x
    invariant forall k :: 0 <= k < pos ==> a[k] < x
    invariant forall k :: pos <= k < i ==> a[k] == x 
    invariant count == count_set(a[..i], x) 
  {
    i := i + 1;
    count := count + 1;
  }
}
// </vc-code>
