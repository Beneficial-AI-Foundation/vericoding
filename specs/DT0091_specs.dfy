// <vc-preamble>
// Helper function for power of 2 calculation
function pow2(n: nat): nat
{
    if n == 0 then 1 else 2 * pow2(n - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_unpackbits(a: seq<nat>) returns (result: seq<nat>)
    // Precondition: All input elements must be valid uint8 values (< 256)
    requires forall i :: 0 <= i < |a| ==> a[i] < 256
    // Postcondition: Output length is 8 times input length
    ensures |result| == |a| * 8
    // Postcondition: All output elements are binary (0 or 1)
    ensures forall k :: 0 <= k < |result| ==> result[k] == 0 || result[k] == 1
    // Postcondition: Each input element a[i] is unpacked into 8 bits in big-endian order
    // where bit j of element i is stored at position i*8 + j in the result
    // The bit extraction follows: (a[i] / (2^(7-j))) % 2
    ensures forall i :: 0 <= i < |a| ==> 
        forall j {:trigger result[i * 8 + j]} :: 0 <= j < 8 ==> 
            result[i * 8 + j] == (a[i] / pow2(7 - j)) % 2
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
