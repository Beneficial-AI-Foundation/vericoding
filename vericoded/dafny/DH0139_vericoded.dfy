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
  var val_a := ValueToReal(a);
  var val_b := ValueToReal(b);
  
  if val_a > val_b {
    result := Some(a);
  } else if val_b > val_a {
    result := Some(b);
  } else {
    result := None;
  }
}
// </vc-code>
