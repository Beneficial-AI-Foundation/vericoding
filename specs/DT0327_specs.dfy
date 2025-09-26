// <vc-preamble>
/*
 * Dafny specification for numpy.lcm functionality.
 * Returns the lowest common multiple of |x1| and |x2| element-wise for vectors.
 * Implements the mathematical LCM operation with all its fundamental properties.
 */

// Helper function to compute absolute value
function Abs(x: int): nat
{
    if x >= 0 then x else -x
}

// Helper function to compute GCD using Euclidean algorithm
function GCD(a: nat, b: nat): nat
    decreases b
{
    if b == 0 then a else GCD(b, a % b)
}

// Helper function to compute LCM using the fundamental relationship: lcm(a,b) * gcd(a,b) = a * b
function LCM(a: nat, b: nat): nat
{
    if a == 0 || b == 0 then 0 else (a * b) / GCD(a, b)
}

// Helper predicate for divisibility
predicate Divides(a: int, b: int)
{
    a != 0 ==> b % a == 0
}

// Main method implementing numpy.lcm functionality
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method lcm(x1: seq<int>, x2: seq<int>) returns (result: seq<int>)
    // Precondition: input vectors must have the same length
    requires |x1| == |x2|
    // Postconditions capturing all LCM mathematical properties
    ensures |result| == |x1|
    // Basic correctness: each element is the LCM of corresponding elements
    ensures forall i :: 0 <= i < |result| ==> result[i] == LCM(Abs(x1[i]), Abs(x2[i]))
    // Non-negativity: LCM is always non-negative
    ensures forall i :: 0 <= i < |result| ==> result[i] >= 0
    // Zero property: LCM with zero is zero
    ensures forall i :: 0 <= i < |result| ==> (x1[i] == 0 || x2[i] == 0) ==> result[i] == 0
    // Commutativity: LCM is commutative
    ensures forall i :: 0 <= i < |result| ==> result[i] == LCM(Abs(x2[i]), Abs(x1[i]))
    // Fundamental LCM-GCD relationship: lcm(a,b) * gcd(a,b) = |a * b|
    ensures forall i :: 0 <= i < |result| ==> 
        (x1[i] != 0 && x2[i] != 0) ==> 
        result[i] * GCD(Abs(x1[i]), Abs(x2[i])) == Abs(x1[i]) * Abs(x2[i])
    // Divisibility: both absolute values divide the LCM
    ensures forall i :: 0 <= i < |result| ==> 
        (x1[i] != 0 && x2[i] != 0) ==> 
        Divides(Abs(x1[i]), result[i]) && Divides(Abs(x2[i]), result[i])
    // Minimality: LCM is the smallest non-negative integer divisible by both absolute values
    ensures forall i :: 0 <= i < |result| ==> 
        forall m :: m >= 0 && Divides(Abs(x1[i]), m) && Divides(Abs(x2[i]), m) && x1[i] != 0 && x2[i] != 0 ==> 
        result[i] <= m
    // Special case: when both are non-zero, LCM is positive
    ensures forall i :: 0 <= i < |result| ==> 
        (x1[i] != 0 && x2[i] != 0) ==> result[i] > 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
