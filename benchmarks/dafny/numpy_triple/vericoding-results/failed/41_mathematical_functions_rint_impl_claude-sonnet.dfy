// <vc-preamble>
// Helper predicate to check if a real number is an integer
ghost predicate IsInteger(x: real)
{
    exists k: int {:trigger k as real} :: x == k as real
}

// Helper predicate to check if a real number is a half-integer (k + 0.5)
ghost predicate IsHalfInteger(x: real)
{
    exists k: int {:trigger (k as real) + 0.5} :: x == (k as real) + 0.5
}

// Helper function to get the integer part of a real number
ghost function IntegerPart(x: real): int
    requires IsInteger(x)
{
    var k :| x == k as real; k
}

// Helper function to get the integer k such that x = k + 0.5
ghost function HalfIntegerBase(x: real): int
    requires IsHalfInteger(x)
{
    var k :| x == (k as real) + 0.5; k
}

// Helper predicate to check if an integer is even
predicate IsEven(k: int)
{
    k % 2 == 0
}

// Main method specification for numpy rint
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified approach with basic floor and manual verification */
function Floor(x: real): int
{
    x.Floor
}

function RintSingle(x: real): real
    ensures IsInteger(RintSingle(x))
{
    var floor_x := Floor(x);
    var frac := x - (floor_x as real);
    if frac == 0.0 then x
    else if frac == 0.5 then
        if IsEven(floor_x) then floor_x as real else (floor_x + 1) as real
    else if frac < 0.5 then floor_x as real
    else (floor_x + 1) as real
}
// </vc-helpers>

// <vc-spec>
method NumpyRint(x: seq<real>) returns (result: seq<real>)
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |x| ==>
        // Result is an integer (represented as real)
        IsInteger(result[i]) &&
        // Difference is at most 0.5
        (result[i] - x[i]) <= 0.5 && (x[i] - result[i]) <= 0.5 &&
        // If input is already integer, output equals input
        (IsInteger(x[i]) ==> result[i] == x[i]) &&
        // For half-integers, round to nearest even
        (IsHalfInteger(x[i]) ==> 
            var k := HalfIntegerBase(x[i]);
            if IsEven(k) then result[i] == k as real
            else result[i] == (k + 1) as real) &&
        // For non-half-integers, round to nearest integer
        (!IsInteger(x[i]) && !IsHalfInteger(x[i]) ==>
            (result[i] - x[i] < 0.5 && result[i] - x[i] > -0.5))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): minimal implementation with basic loop */
{
    result := [];
    var i := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant |result| == i
    {
        var floor_x := Floor(x[i]);
        var frac := x[i] - (floor_x as real);
        var rounded: real;
        if frac == 0.0 {
            rounded := x[i];
        } else if frac == 0.5 {
            if IsEven(floor_x) {
                rounded := floor_x as real;
            } else {
                rounded := (floor_x + 1) as real;
            }
        } else if frac < 0.5 {
            rounded := floor_x as real;
        } else {
            rounded := (floor_x + 1) as real;
        }
        result := result + [rounded];
        i := i + 1;
    }
}
// </vc-code>
