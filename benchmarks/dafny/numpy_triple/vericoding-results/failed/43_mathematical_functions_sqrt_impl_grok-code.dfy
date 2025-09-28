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
/* helper modified by LLM (iteration 5): updated sqrt_float postcondition for simplicity */
/* helper modified by LLM (iteration 2): implemented ghost sqrt and helper sqrt_float */
ghost function sqrt(x: real): (result: real)
  requires x >= 0.0
  ensures result * result == x && result >= 0.0
{
  x ^ (1.0 / 2.0)
}

function sqrt_float(x: Float): Float
  ensures x.NaN? ==> result.NaN?
  ensures x.Real? && x.value < 0.0 ==> result.NaN?
  ensures x.Real? && x.value >= 0.0 ==> result.Real? && result.value * result.value == x.value && result.value >= 0.0
{
  match x {
    case NaN => NaN
    case Real(v) => if v < 0.0 then NaN else Real(v ^ (1.0 / 2.0))
  }
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
/* code modified by LLM (iteration 5): fixed syntax error in sequence comprehension by removing type annotation */
{
  var new_elements := seq(i | 0 <= i < x.length :: sqrt_float(x.get(i)));
  result := Vector(new_elements, x.length);
}
// </vc-code>
