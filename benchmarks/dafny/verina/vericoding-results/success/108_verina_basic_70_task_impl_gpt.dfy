// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ExistsFromIPlus1(a: seq<int>, p: int -> bool, i: int)
  requires 0 <= i < |a|
  requires (exists j :: i <= j < |a| && p(a[j]))
  requires !p(a[i])
  ensures (exists j :: i+1 <= j < |a| && p(a[j]))
{
  var j: int :| i <= j < |a| && p(a[j]);
  if j == i {
    assert p(a[i]);
    assert false;
  }
  assert i + 1 <= j;
  assert exists j2 :: i + 1 <= j2 < |a| && p(a[j2]);
}
// </vc-helpers>

// <vc-spec>
method LinearSearch3(a: seq<int>, p: int -> bool) returns (result: nat)
    requires 
        exists i :: 0 <= i < |a| && p(a[i])
    ensures 
        result < |a| &&
        p(a[result]) &&
        forall k :: 0 <= k < result ==> !p(a[k])
// </vc-spec>
// <vc-code>
{
  var i: int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> !p(a[k])
    invariant exists j :: i <= j < |a| && p(a[j])
    decreases |a| - i
  {
    if p(a[i]) {
      result := i;
      return;
    }
    ExistsFromIPlus1(a, p, i);
    i := i + 1;
  }
  assert false;
}
// </vc-code>
