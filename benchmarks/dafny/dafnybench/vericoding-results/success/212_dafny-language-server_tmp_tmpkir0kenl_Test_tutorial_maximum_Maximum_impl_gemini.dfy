// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
// </vc-spec>
// <vc-code>
{
  max := values[0];
  var i := 1;
  while i < |values|
    invariant 1 <= i <= |values|
    invariant max in values[..i]
    invariant forall k :: 0 <= k < i ==> values[k] <= max
  {
    if values[i] > max {
      max := values[i];
    }
    i := i + 1;
  }
}
// </vc-code>
