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
/* helper modified by LLM (iteration 2): lemma showing that an int cast to real satisfies IsInteger */
lemma IntAsRealIsInteger(k: int)
  ensures IsInteger(k as real)
{
  assert exists t: int :: k as real == t as real;
}

/* helper modified by LLM (iteration 2): function rounding a real to the nearest integer with ties to even */
function RoundEvenReal(x: real): real
{
  if IsInteger(x) then x
  else if IsHalfInteger(x) then
    var k := HalfIntegerBase(x);
    if IsEven(k) then k as real else (k + 1) as real
  else
    var k: int :| x - k as real < 0.5 && k as real - x < 0.5;
    k as real
}

/* helper modified by LLM (iteration 2): lemma establishing properties of RoundEvenReal */
lemma RoundEvenRealProps(x: real)
  ensures IsInteger(RoundEvenReal(x))
  ensures (RoundEvenReal(x) - x) <= 0.5 && (x - RoundEvenReal(x)) <= 0.5
  ensures IsInteger(x) ==> RoundEvenReal(x) == x
  ensures IsHalfInteger(x) ==>
    (var k := HalfIntegerBase(x);
     if IsEven(k) then RoundEvenReal(x) == k as real else RoundEvenReal(x) == (k + 1) as real)
  ensures !IsInteger(x) && !IsHalfInteger(x) ==> (RoundEvenReal(x) - x < 0.5 && RoundEvenReal(x) - x > -0.5)
{
  if IsInteger(x) {
    // Round to itself
  } else if IsHalfInteger(x) {
    var k := HalfIntegerBase(x);
    assert x == (k as real) + 0.5;
    if IsEven(k) {
      assert RoundEvenReal(x) == k as real;
      assert IsInteger(RoundEvenReal(x)) by { IntAsRealIsInteger(k); }
      assert (RoundEvenReal(x) - x) == -0.5;
      assert (x - RoundEvenReal(x)) == 0.5;
    } else {
      assert RoundEvenReal(x) == (k + 1) as real;
      assert IsInteger(RoundEvenReal(x)) by { IntAsRealIsInteger(k + 1); }
      assert (RoundEvenReal(x) - x) == 0.5;
      assert (x - RoundEvenReal(x)) == -0.5;
    }
  } else {
    var k: int :| x - k as real < 0.5 && k as real - x < 0.5;
    assert RoundEvenReal(x) == k as real;
    assert IsInteger(RoundEvenReal(x)) by { IntAsRealIsInteger(k); }
    assert (RoundEvenReal(x) - x) < 0.5 && (x - RoundEvenReal(x)) < 0.5;
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
  /* code modified by LLM (iteration 2): build result using a loop to avoid comprehension parse issues and invoke lemma for properties */
  var res: seq<real> := [];
  var i: int := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == RoundEvenReal(x[j])
  {
    res := res + [RoundEvenReal(x[i])];
    i := i + 1;
  }
  result := res;

  // Help the verifier with per-element properties
  forall k | 0 <= k < |x| {
    RoundEvenRealProps(x[k]);
  }
}
// </vc-code>
