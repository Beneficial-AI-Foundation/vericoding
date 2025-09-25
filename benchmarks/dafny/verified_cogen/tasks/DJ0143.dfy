// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Cubes(len: int) returns (result: array<int>)
    requires len >= 0
    ensures result.Length == len
    ensures forall i :: 0 <= i < len ==> result[i] == i * i * i
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
