// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ExistsIndexAfterIncrement(a: seq<int>, p: int -> bool, i: int)
  requires 0 <= i < |a|
  requires exists j :: i <= j < |a| && p(a[j])
  requires !p(a[i])
  ensures exists j :: i + 1 <= j < |a| && p(a[j])
{
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
  var i := 0;
  // Maintain that all indices < i do not satisfy p, and there exists a witness >= i
  while i < |a| && !p(a[i])
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> !p(a[k])
    invariant exists j :: i <= j < |a| && p(a[j])
    decreases |a| - i
  {
    i := i + 1;
  }
  result := i;
}

// </vc-code>
