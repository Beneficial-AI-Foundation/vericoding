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
/* helper modified by LLM (iteration 5): fixed parse error by removing let-in from ensures clause */
function RoundReal(r: real): real
    ensures IsInteger(result)
    ensures (result - r) <= 0.5 && (r - result) <= 0.5
    ensures IsInteger(r) ==> result == r
    ensures IsHalfInteger(r) ==>
        (if IsEven(HalfIntegerBase(r))
        then result == HalfIntegerBase(r) as real
        else result == (HalfIntegerBase(r) + 1) as real)
    ensures !IsInteger(r) && !IsHalfInteger(r) ==>
        (result - r < 0.5 && result - r > -0.5)
{
    if IsInteger(r) then
        r
    else if IsHalfInteger(r) then
        let k := HalfIntegerBase(r) in
        if IsEven(k) then k as real else (k + 1) as real
    else
        (r + 0.5).Floor as real
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
/* code modified by LLM (iteration 5): fixed parse error by removing let-in from invariant */
{
  var res_array := new real[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < i ==> res_array[j] == RoundReal(x[j])
    invariant forall j :: 0 <= j < i ==> 
        IsInteger(res_array[j]) &&
        (res_array[j] - x[j]) <= 0.5 && (x[j] - res_array[j]) <= 0.5 &&
        (IsInteger(x[j]) ==> res_array[j] == x[j]) &&
        (IsHalfInteger(x[j]) ==> 
            (if IsEven(HalfIntegerBase(x[j]))
             then res_array[j] == HalfIntegerBase(x[j]) as real
             else res_array[j] == (HalfIntegerBase(x[j]) + 1) as real)) &&
        (!IsInteger(x[j]) && !IsHalfInteger(x[j]) ==>
            (res_array[j] - x[j] < 0.5 && res_array[j] - x[j] > -0.5))
  {
    res_array[i] := RoundReal(x[i]);
    i := i + 1;
  }
  result := res_array[..];
}
// </vc-code>
