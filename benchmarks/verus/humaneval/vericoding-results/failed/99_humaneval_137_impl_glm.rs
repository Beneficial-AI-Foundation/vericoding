// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub enum Value {
    Int(int),
    Real(int), /* Using int to represent reals for simplicity */
    Str(String),
}

spec fn is_valid_numeric_string(s: String) -> bool {
    true
}

spec fn value_to_real(v: Value) -> int {
    match v {
        Value::Int(i) => i,
        Value::Real(r) => r,
        Value::Str(s) => string_to_real(s),
    }
}

spec fn string_to_real(s: String) -> int {
    0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed integer literal type */
exec fn value_to_int(v: Value) -> int {
    match v {
        Value::Int(i) => i,
        Value::Real(r) => r,
        Value::Str(s) => 0i,
    }
}

proof fn value_to_int_equals_spec(v: Value)
    ensures value_to_int(v) == value_to_real(v)
{
    match v {
        Value::Int(i) => {
            assert(value_to_real(v) == i);
        }
        Value::Real(r) => {
            assert(value_to_real(v) == r);
        }
        Value::Str(s) => {
            assert(value_to_real(v) == string_to_real(s));
            assert(string_to_real(s) == 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn compare_one(a: Value, b: Value) -> (result: Option<Value>)
    requires 
        matches!(a, Value::Str(_)) ==> is_valid_numeric_string(a.arrow_Str_0()),
        matches!(b, Value::Str(_)) ==> is_valid_numeric_string(b.arrow_Str_0()),
    ensures 
        value_to_real(a) == value_to_real(b) <==> matches!(result, Option::None),
        value_to_real(a) > value_to_real(b) <==> result == Some(a),
        value_to_real(b) > value_to_real(a) <==> result == Some(b),
        matches!(result, Option::Some(_)) ==> (result.arrow_Some_0() == a || result.arrow_Some_0() == b),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented comparison logic */
    let a_val = value_to_int(a);
    let b_val = value_to_int(b);
    proof {
        value_to_int_equals_spec(a);
        value_to_int_equals_spec(b);
    }
    if a_val == b_val {
        None
    } else if a_val > b_val {
        Some(a)
    } else {
        Some(b)
    }
}
// </vc-code>


}

fn main() {}