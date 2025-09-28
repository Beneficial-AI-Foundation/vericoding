// <vc-preamble>
// Ghost functions for mathematical operations (axiomatized)
function {:axiom} RealSin(x: real): real
{
    0.0  // Placeholder implementation for compilation
}

function {:axiom} RealPi(): real
    ensures RealPi() > 3.14 && RealPi() < 3.15
{
    3.141592653589793  // Placeholder implementation for compilation
}

// Helper function to define the mathematical sinc function
function SincValue(x: real): real
{
    if x == 0.0 then 1.0
    else (RealSin(RealPi() * x)) / (RealPi() * x)
}

// Main method specification for element-wise sinc computation
// Helper predicate to check if a real number is an integer
ghost predicate IsInteger(x: real)
{
    exists k: int {:trigger k as real} :: x == k as real
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Provided proof for SincSymmetry assuming RealSin is an odd function. */
lemma SincSymmetry(y: real)
    ensures SincValue(y) == SincValue(-y)
{
    if y == 0.0 {
        // The property holds trivially for y = 0.0
    } else {
        // For y != 0.0, the proof relies on the (assumed) property that RealSin is an odd function.
        // i.e., RealSin(-z) == -RealSin(z).
        calc {
            SincValue(-y);
        ==  // Definition of SincValue for non-zero argument
            (RealSin(RealPi() * -y)) / (RealPi() * -y);
        ==  // Algebraic property of multiplication
            (RealSin(-(RealPi() * y))) / -(RealPi() * y);
        ==  // RealSin is an odd function (assumed property)
            -RealSin(RealPi() * y) / -(RealPi() * y);
        ==  // (-a / -b) == (a / b)
            RealSin(RealPi() * y) / (RealPi() * y);
        ==  // Definition of SincValue for non-zero argument
            SincValue(y);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method Sinc(x: seq<real>) returns (result: seq<real>)
    // No preconditions needed - sinc is defined for all real numbers
    ensures |result| == |x|
    // Element-wise computation: each result[i] equals sinc of x[i]
    ensures forall i :: 0 <= i < |x| ==> result[i] == SincValue(x[i])
    // Maximum at zero: sinc(0) = 1
    ensures forall i :: 0 <= i < |x| && x[i] == 0.0 ==> result[i] == 1.0
    // Symmetry property: sinc(-x) = sinc(x) for corresponding elements
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] == -x[j] ==> result[i] == result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Replaced seq comprehension with a while loop to fix a compilation error. */
{
    var res := new real[|x|];
    var i: nat := 0;
    while i < |x|
        invariant i <= |x|
        invariant forall j: nat :: j < i ==> res[j] == SincValue(x[j])
    {
        res[i] := SincValue(x[i]);
        i := i + 1;
    }
    result := res[..];
}
// </vc-code>
