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

function RealEqual(r1: real, r2: real): bool
{
  r1 == r2
}

lemma RealComparisonLemma(r1: real, r2: real)
  ensures (r1 == r2) <==> RealEqual(r1, r2)
  ensures (r1 > r2) <==> !RealEqual(r1, r2) && r1 > r2
  ensures (r2 > r1) <==> !RealEqual(r1, r2) && r2 > r1
{
}

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
    /* code modified by LLM (iteration 3): Simplify comparison using direct equality and inequality */
    var ra := ValueToReal(a);
    var rb := ValueToReal(b);
    
    if ra == rb {
        result := None;
    } else if ra > rb {
        result := Some(a);
    } else {
        result := Some(b);
    }
  }
// </vc-code>
