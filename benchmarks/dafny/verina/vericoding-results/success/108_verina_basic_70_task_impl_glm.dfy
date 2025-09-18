// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix index out of range by ensuring j < |a| */
predicate NoTrueInPrefix(a: seq<int>, p: int -> bool, i: nat) { forall j :: 0 <= j < i && j < |a| ==> !p(a[j]) }
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
/* code modified by LLM (iteration 2): no changes needed */
{
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant NoTrueInPrefix(a, p, i)
    invariant exists j :: i <= j < |a| && p(a[j])
  {
    if p(a[i]) {
      break;
    }
    i := i + 1;
  }
  result := i;
}
// </vc-code>
