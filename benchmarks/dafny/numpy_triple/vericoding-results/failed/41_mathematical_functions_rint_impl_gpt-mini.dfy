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
/* helper modified by LLM (iteration 5): non-ghost predicate for integer check */
predicate IsIntegerRT(x: real)
{
  exists k: int {:trigger k as real} :: x == k as real
}

/* helper modified by LLM (iteration 5): non-ghost predicate for half-integer check */
predicate IsHalfIntegerRT(x: real)
{
  exists k: int {:trigger (k as real) + 0.5} :: x == (k as real) + 0.5
}

/* helper modified by LLM (iteration 5): function method to extract integer part when x is integer */
function method IntegerPartRT(x: real): int
  requires IsIntegerRT(x)
{
  var k :| x == k as real; k
}

/* helper modified by LLM (iteration 5): function method to extract base k when x = k + 0.5 */
function method HalfIntegerBaseRT(x: real): int
  requires IsHalfIntegerRT(x)
{
  var k :| x == (k as real) + 0.5; k
}

/* helper modified by LLM (iteration 5): function method to choose nearest integer for non-half non-integer cases */
function method RoundNearestIntBaseRT(x: real): int
  requires !IsIntegerRT(x) && !IsHalfIntegerRT(x)
  ensures (x - (RoundNearestIntBaseRT(x) as real)) < 0.5 && ((RoundNearestIntBaseRT(x) as real) - x) < 0.5
{
  var k :| (x - (k as real)) < 0.5 && ((k as real) - x) < 0.5; k
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
  /* code modified by LLM (iteration 5): implement elementwise rounding using runtime helpers */
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
      (!IsInteger(x[j]) && !IsHalfInteger(x[j]) ==> (result[j] - x[j] < 0.5 && result[j] - x[j] > -0.5))
  {
    var xi := x[i];
    var ri: real;
    if IsIntegerRT(xi) {
      ri := xi;
    } else if IsHalfIntegerRT(xi) {
      var k := HalfIntegerBaseRT(xi);
      if IsEven(k) {
        ri := (k as real);
      } else {
        ri := ((k + 1) as real);
      }
    } else {
      var k := RoundNearestIntBaseRT(xi);
      ri := (k as real);
    }
    result := result + [ri];
    i := i + 1;
  }
}

// </vc-code>
