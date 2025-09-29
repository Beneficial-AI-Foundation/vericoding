// <vc-preamble>
/*
 * Dafny specification for numpy.prod: Return the product of array elements.
 * 
 * Computes the product of all elements in a sequence. For empty sequences,
 * returns 1.0 as the identity element of multiplication.
 * 
 * Note: This specification models floating-point behavior using real numbers.
 * In practice, this would operate on floating-point values with associated
 * precision and rounding behavior.
 */

// Helper function to compute left-fold product of sequence elements
// Models floating-point product computation with left-associative fold
function SeqProductLeftAux(s: seq<real>, acc: real, index: nat): real
    requires index <= |s|
    decreases |s| - index
{
    if index == |s| then acc
    else SeqProductLeftAux(s, acc * s[index], index + 1)
}

// Helper function to compute product of sequence elements
// Models floating-point product computation using left-fold semantics
function SeqProduct(s: seq<real>): real
{
    SeqProductLeftAux(s, 1.0, 0)
}

// Helper predicate to check if any element in sequence is zero
predicate ContainsZero(s: seq<real>)
{
    exists i :: 0 <= i < |s| && s[i] == 0.0
}

// Main product computation method
// Models numpy.prod behavior with floating-point semantics
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Prod(a: seq<real>) returns (result: real)
    ensures result == SeqProduct(a)
    ensures |a| == 0 ==> result == 1.0
    ensures ContainsZero(a) ==> result == 0.0
    ensures |a| > 0 && !ContainsZero(a) ==> result != 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
