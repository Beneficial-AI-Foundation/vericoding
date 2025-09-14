// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun2(x: array<int>) 
    requires 
        forall k:int :: 0 <= k < x.Length ==> x[k] <= 0x7FFF_FFFB
    ensures 
        forall k:int :: 0 <= k < x.Length ==> x[k] == old(x[k]) + 4
    modifies x
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added invariant for unmodified array elements to assist loop invariant proof */
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall k :: 0 <= k < i ==> x[k] == old(x[k]) + 4
    invariant forall k :: i <= k < x.Length ==> x[k] == old(x[k])
  {
    x[i] := x[i] + 4;
    i := i + 1;
  }
}
// </vc-code>
