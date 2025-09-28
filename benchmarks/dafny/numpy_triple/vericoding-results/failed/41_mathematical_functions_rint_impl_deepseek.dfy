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
/* helper modified by LLM (iteration 5): Fixed floor/ceil to use proper integer casting and return real values */
function floor(x: real): real
    ensures IsInteger(floor(x))
{
    var intVal: int := if x >= 0.0 then x as int else (x - 1.0) as int;
    intVal as real
}

function ceil(x: real): real
    ensures IsInteger(ceil(x))
{
    var intVal: int := if x <= 0.0 then x as int else (x + 1.0) as int;
    intVal as real
}

function ComputeResultValue(x: real): (r: real)
    ensures IsInteger(r)
    ensures r - x <= 0.5 && x - r <= 0.5
    ensures IsInteger(x) ==> r == x
    ensures IsHalfInteger(x) ==> 
        var k := HalfIntegerBase(x);
        if IsEven(k) then r == k as real
        else r == (k + 1) as real
    ensures !IsInteger(x) && !IsHalfInteger(x) ==> (r - x < 0.5 && r - x > -0.5)
{
    if IsInteger(x) then
        x
    else if IsHalfInteger(x) then
        var k := HalfIntegerBase(x);
        if IsEven(k) then
            k as real
        else
            (k + 1) as real
    else
        var f := floor(x);
        var c := ceil(x);
        if x - f < c - x then
            f
        else if c - x < x - f then
            c
        else
            if IsEven(f as int) then f else c
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
/* code modified by LLM (iteration 5): Fixed array initialization and sequence assignment */
{
    result := new real[|x|];
    var i := 0;
    var tempResult := result;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant |tempResult| == |x|
        invariant forall j :: 0 <= j < i ==> IsInteger(tempResult[j])
        invariant forall j :: 0 <= j < i ==> tempResult[j] - x[j] <= 0.5 && x[j] - tempResult[j] <= 0.5
        invariant forall j :: 0 <= j < i ==> (IsInteger(x[j]) ==> tempResult[j] == x[j])
        invariant forall j :: 0 <= j < i ==> (IsHalfInteger(x[j]) ==>
            var k_val := HalfIntegerBase(x[j]);
            if IsEven(k_val) then tempResult[j] == k_val as real
            else tempResult[j] == (k_val + 1) as real)
        invariant forall j :: 0 <= j < i ==> (!IsInteger(x[j]) && !IsHalfInteger(x[j]) ==> 
            (tempResult[j] - x[j] < 0.5 && tempResult[j] - x[j] > -0.5))
    {
        tempResult := tempResult[i := ComputeResultValue(x[i])];
        i := i + 1;
    }
    result := tempResult;
}
// </vc-code>
