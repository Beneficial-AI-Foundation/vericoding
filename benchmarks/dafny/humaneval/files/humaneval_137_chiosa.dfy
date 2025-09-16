// <vc-preamble>
// ======= TASK =======
// Create a function that compares two values and returns the larger one in its original format.
// Values can be integers, reals, or strings representing real numbers (with '.' or ',' as decimal separators).
// Return None if the values are numerically equal.

// ======= SPEC REQUIREMENTS =======
datatype Value = Int(i: int) | Real(r: real) | Str(s: string)

datatype Option<T> = None | Some(value: T)

predicate IsValidNumericString(s: string)
{
    true
}

function ValueToReal(v: Value): real
    requires v.Str? ==> IsValidNumericString(v.s)
{
    match v {
        case Int(i) => i as real
        case Real(r) => r
        case Str(s) => StringToReal(s)
    }
}

function StringToReal(s: string): real
    requires IsValidNumericString(s)
{
    0.0
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
method compare_one(a: Value, b: Value) returns (result: Option<Value>)
    requires (a.Str? ==> IsValidNumericString(a.s))
    requires (b.Str? ==> IsValidNumericString(b.s))
    ensures ValueToReal(a) == ValueToReal(b) <==> result == None
    ensures ValueToReal(a) > ValueToReal(b) <==> result == Some(a)
    ensures ValueToReal(b) > ValueToReal(a) <==> result == Some(b)
    ensures result.Some? ==> (result.value == a || result.value == b)
// </vc-spec>
// <vc-code>
{
    var num_a := ValueToReal(a);
    var num_b := ValueToReal(b);

    if num_a == num_b {
        result := None;
    } else if num_a > num_b {
        result := Some(a);
    } else {
        result := Some(b);
    }
}
// </vc-code>
