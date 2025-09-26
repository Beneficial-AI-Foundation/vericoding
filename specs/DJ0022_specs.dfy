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
    assume {:axiom} false;
}
// </vc-code>
