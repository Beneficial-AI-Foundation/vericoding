// <vc-preamble>
// Float datatype that can represent NaN for negative inputs
datatype Float = Real(value: real) | NaN

// Vector represented as a sequence with a fixed length
datatype Vector<T> = Vector(elements: seq<T>, length: nat)
{
    predicate Valid() {
        |elements| == length
    }
    
    function get(i: nat): T
        requires Valid()
        requires i < length
    {
        elements[i]
    }
}

// Helper predicate to check if a Float is non-negative
predicate NonNegative(x: Float) {
    x.Real? && x.value >= 0.0
}

// Helper predicate to check if a Float is NaN
predicate IsNaN(x: Float) {
    x.NaN?
}
// </vc-preamble>

// <vc-helpers>
function NewtonSqrt(n: real, guess: real): real
  requires n >= 0.0
  requires guess > 0.0
  ensures NewtonSqrt(n, guess) >= 0.0
  ensures NewtonSqrt(n, guess) * NewtonSqrt(n, guess) == n
  decreases if abs(guess * guess - n) < 0.0 then 0.0 else abs(guess * guess - n)
{
  if abs(guess * guess - n) < 0.000000001 then
    guess
  else
    NewtonSqrt(n, (guess + n / guess) / 2.0)
}

function abs(x: real): real
{
  if x >= 0.0 then x else -x
}

function max(a: real, b: real): real
{
  if a > b then a else b
}

function sqrtSingle(x: Float): Float
  ensures x.Real? && x.value >= 0.0 ==> sqrtSingle(x).Real? && abs(sqrtSingle(x).value * sqrtSingle(x).value - x.value) < 0.000001
  ensures x.Real? && x.value < 0.0 ==> sqrtSingle(x).NaN?
  ensures x.NaN? ==> sqrtSingle(x).NaN?
  ensures x.Real? && x.value == 0.0 ==> sqrtSingle(x).Real? && sqrtSingle(x).value == 0.0
  ensures x.Real? && x.value == 1.0 ==> sqrtSingle(x).Real? && sqrtSingle(x).value == 1.0
{
  if x.NaN? then
    NaN
  else if x.value < 0.0 then
    NaN
  else if x.value == 0.0 then
    Real(0.0)
  else if x.value == 1.0 then
    Real(1.0)
  else
    Real(NewtonSqrt(x.value, max(x.value / 2.0, 0.1)))
}
// </vc-helpers>

// <vc-spec>
method sqrt(x: Vector<Float>) returns (result: Vector<Float>)
    requires x.Valid()
    ensures result.Valid()
    ensures result.length == x.length
    // For non-negative inputs: result² = input and result ≥ 0
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value >= 0.0 ==>
        result.get(i).Real? && result.get(i).value * result.get(i).value == x.get(i).value && result.get(i).value >= 0.0
    // For negative inputs: result is NaN
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value < 0.0 ==>
        result.get(i).NaN?
    // NaN inputs produce NaN outputs
    ensures forall i :: 0 <= i < x.length && x.get(i).NaN? ==>
        result.get(i).NaN?
    // Special cases
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value == 0.0 ==>
        result.get(i).Real? && result.get(i).value == 0.0
    ensures forall i :: 0 <= i < x.length && x.get(i).Real? && x.get(i).value == 1.0 ==>
        result.get(i).Real? && result.get(i).value == 1.0
    // Monotonicity on non-negative inputs
    ensures forall i, j :: (0 <= i < x.length && 0 <= j < x.length &&
        x.get(i).Real? && x.get(j).Real? && 
        x.get(i).value >= 0.0 && x.get(j).value >= 0.0 && x.get(i).value <= x.get(j).value) ==>
        result.get(i).Real? && result.get(j).Real? && result.get(i).value <= result.get(j).value
    // Shape preservation is guaranteed by the length equality
// </vc-spec>
// <vc-code>
{
  var elements := new Float[x.length];
  var i := 0;
  while i < x.length
    invariant i <= x.length
    invariant |elements[..]| == x.length
    invariant forall j :: 0 <= j < i ==> elements[j] == sqrtSingle(x.get(j))
  {
    elements[i] := sqrtSingle(x.get(i));
    i := i + 1;
  }
  result := Vector(elements[..], x.length);
}
// </vc-code>
