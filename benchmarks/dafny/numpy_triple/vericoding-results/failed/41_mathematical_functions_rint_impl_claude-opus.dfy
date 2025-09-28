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
/* helper modified by LLM (iteration 5): Fixed strict inequality proofs in lemma */
function RoundToNearestEven(x: real): real
{
    var lower := x.Floor as real;
    var upper := lower + 1.0;
    
    if x == lower then
        // Already an integer
        lower
    else if x == lower + 0.5 then
        // Half-integer case: round to nearest even
        if x.Floor % 2 == 0 then lower else upper
    else if x - lower < 0.5 then
        // Closer to lower
        lower
    else
        // Closer to upper
        upper
}

/* helper modified by LLM (iteration 5): Added explicit proofs for strict inequalities */
lemma RoundToNearestEvenProperties(x: real)
    ensures var r := RoundToNearestEven(x);
        IsInteger(r) &&
        (r - x) <= 0.5 && (x - r) <= 0.5 &&
        (IsInteger(x) ==> r == x) &&
        (IsHalfInteger(x) ==> 
            var k := HalfIntegerBase(x);
            if IsEven(k) then r == k as real
            else r == (k + 1) as real) &&
        (!IsInteger(x) && !IsHalfInteger(x) ==>
            (r - x < 0.5 && r - x > -0.5))
{
    var lower := x.Floor as real;
    var upper := lower + 1.0;
    var r := RoundToNearestEven(x);
    
    // Establish that lower is an integer
    assert lower == x.Floor as real;
    
    // Establish that upper is an integer
    assert upper == (x.Floor + 1) as real;
    
    if x == lower {
        assert r == lower;
        assert IsInteger(x);
        assert r == x;
    } else if x == lower + 0.5 {
        // x is a half-integer with base x.Floor
        var k := x.Floor;
        assert x == k as real + 0.5;
        assert IsHalfInteger(x);
        if k % 2 == 0 {
            assert r == lower;
            assert r == k as real;
        } else {
            assert r == upper;
            assert r == (k + 1) as real;
        }
    } else if x - lower < 0.5 {
        assert r == lower;
        assert !IsInteger(x) && !IsHalfInteger(x);
        assert r - x == lower - x;
        assert x - lower > 0;  // Since x != lower
        assert r - x < 0;       // Since r == lower and x > lower
        assert r - x > -0.5;    // Since x - lower < 0.5
    } else {
        assert r == upper;
        assert !IsInteger(x) && !IsHalfInteger(x);
        assert r - x == upper - x;
        assert r - x == (lower + 1.0) - x;
        assert x - lower > 0.5; // From the else condition
        assert x < upper;       // Since x.Floor == lower means x < lower + 1
        assert r - x > 0;       // Since r == upper and x < upper
        assert r - x < 0.5;     // Since upper - x < 0.5 when x > lower + 0.5
    }
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
{
  /* code modified by LLM (iteration 5): Same implementation with lemma call */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
        IsInteger(result[j]) &&
        (result[j] - x[j]) <= 0.5 && (x[j] - result[j]) <= 0.5 &&
        (IsInteger(x[j]) ==> result[j] == x[j]) &&
        (IsHalfInteger(x[j]) ==> 
            var k := HalfIntegerBase(x[j]);
            if IsEven(k) then result[j] == k as real
            else result[j] == (k + 1) as real) &&
        (!IsInteger(x[j]) && !IsHalfInteger(x[j]) ==>
            (result[j] - x[j] < 0.5 && result[j] - x[j] > -0.5))
  {
    var rounded := RoundToNearestEven(x[i]);
    RoundToNearestEvenProperties(x[i]);
    result := result + [rounded];
    i := i + 1;
  }
}
// </vc-code>
