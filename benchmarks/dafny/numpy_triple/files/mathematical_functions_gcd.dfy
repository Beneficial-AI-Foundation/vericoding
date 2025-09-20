// <vc-preamble>
// Helper function to compute absolute value
function Abs(x: int): int
{
    if x >= 0 then x else -x
}

// Helper function to compute GCD of two natural numbers
function GCD(a: nat, b: nat): nat
{
    if b == 0 then a else GCD(b, a % b)
}

// Helper predicate to check if d divides n
ghost predicate Divides(d: int, n: int)
{
    exists k: int :: n == d * k
}

// Main method implementing numpy.gcd functionality
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_gcd(x1: seq<int>, x2: seq<int>) returns (result: seq<int>)
    requires |x1| == |x2|
    ensures |result| == |x1|
    // Each result element is the GCD of corresponding input elements' absolute values
    ensures forall i :: 0 <= i < |result| ==> result[i] == GCD(Abs(x1[i]) as nat, Abs(x2[i]) as nat) as int
    // Result elements are non-negative
    ensures forall i :: 0 <= i < |result| ==> result[i] >= 0
    // Special case: gcd(0, 0) = 0
    ensures forall i :: 0 <= i < |result| && x1[i] == 0 && x2[i] == 0 ==> result[i] == 0
    // Special case: gcd(a, 0) = |a| for non-zero a
    ensures forall i :: 0 <= i < |result| && x1[i] != 0 && x2[i] == 0 ==> result[i] == Abs(x1[i])
    // Special case: gcd(0, b) = |b| for non-zero b
    ensures forall i :: 0 <= i < |result| && x1[i] == 0 && x2[i] != 0 ==> result[i] == Abs(x2[i])
    // Divisibility: gcd divides both operands
    ensures forall i :: 0 <= i < |result| ==> Divides(result[i], x1[i]) && Divides(result[i], x2[i])
    // Greatest property: any common divisor also divides the gcd
    ensures forall i, d :: 0 <= i < |result| && Divides(d, x1[i]) && Divides(d, x2[i]) ==> Divides(d, result[i])
    // Commutativity: gcd(a,b) = gcd(b,a)
    ensures forall i :: 0 <= i < |result| ==> GCD(Abs(x1[i]) as nat, Abs(x2[i]) as nat) == GCD(Abs(x2[i]) as nat, Abs(x1[i]) as nat)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
