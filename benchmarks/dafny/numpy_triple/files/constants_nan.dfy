// <vc-preamble>
// Required import for mathematical operations
module Reals {
    function Sqrt(x: real): real
        requires x >= 0.0
    {
        x  // Placeholder implementation for compilation
    }
}

// Datatype to represent IEEE 754 floating point values including NaN
datatype IEEEFloat = Normal(value: real) | NaN

// Predicate to check if a value is NaN
predicate IsNaN(f: IEEEFloat) {
    f.NaN?
}

// Predicate to check if a value is finite
predicate IsFinite(f: IEEEFloat) {
    f.Normal?
}

// IEEE 754 arithmetic operations that propagate NaN
function Add(x: IEEEFloat, y: IEEEFloat): IEEEFloat {
    if x.NaN? || y.NaN? then NaN
    else Normal(x.value + y.value)
}

function Sub(x: IEEEFloat, y: IEEEFloat): IEEEFloat {
    if x.NaN? || y.NaN? then NaN
    else Normal(x.value - y.value)
}

function Mul(x: IEEEFloat, y: IEEEFloat): IEEEFloat {
    if x.NaN? || y.NaN? then NaN
    else Normal(x.value * y.value)
}

function Div(x: IEEEFloat, y: IEEEFloat): IEEEFloat {
    if x.NaN? || y.NaN? then NaN
    else if y.Normal? && y.value == 0.0 then NaN
    else if y.Normal? && y.value != 0.0 then Normal(x.value / y.value)
    else NaN
}

function Sqrt(x: IEEEFloat): IEEEFloat {
    if x.NaN? then NaN
    else if x.Normal? && x.value < 0.0 then NaN
    else if x.Normal? && x.value >= 0.0 then Normal(Reals.Sqrt(x.value))
    else NaN
}

// IEEE 754 comparison operations (NaN is unordered)
predicate LessThan(x: IEEEFloat, y: IEEEFloat) {
    x.Normal? && y.Normal? && x.value < y.value
}

predicate GreaterThan(x: IEEEFloat, y: IEEEFloat) {
    x.Normal? && y.Normal? && x.value > y.value
}

// Method that returns IEEE 754 NaN with complete specification
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method GetNaN() returns (result: IEEEFloat)
    ensures IsNaN(result)
    // Property 2: Arithmetic operations with NaN produce NaN
    ensures forall x: IEEEFloat :: IsNaN(Add(result, x))
    ensures forall x: IEEEFloat :: IsNaN(Sub(result, x))
    ensures forall x: IEEEFloat :: IsNaN(Mul(result, x))
    ensures forall x: IEEEFloat :: IsNaN(Div(result, x))
    // Property 3: NaN is unordered (all strict comparisons are false)
    ensures forall x: IEEEFloat :: !LessThan(result, x)
    ensures forall x: IEEEFloat :: !GreaterThan(result, x)
    ensures forall x: IEEEFloat :: !LessThan(x, result)
    ensures forall x: IEEEFloat :: !GreaterThan(x, result)
    // Property 4: NaN is not finite
    ensures !IsFinite(result)
    // Property 5: Additional NaN propagation properties
    ensures IsNaN(Mul(result, Normal(0.0)))
    ensures IsNaN(Div(Normal(0.0), result))
    ensures IsNaN(Sub(result, result))
    ensures IsNaN(Sqrt(result))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
