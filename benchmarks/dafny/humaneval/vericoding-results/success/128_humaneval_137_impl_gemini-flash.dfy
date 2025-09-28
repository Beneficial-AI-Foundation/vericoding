// <vc-preamble>

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
// No helpers needed for this problem.
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
    var a_real := ValueToReal(a);
    var b_real := ValueToReal(b);

    if a_real == b_real {
        result := None;
    } else if a_real > b_real {
        result := Some(a);
    } else {
        result := Some(b);
    }
}
// </vc-code>
