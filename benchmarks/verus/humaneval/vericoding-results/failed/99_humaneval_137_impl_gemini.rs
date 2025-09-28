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
/* helper modified by LLM (iteration 5): fixed compilation error on integer literal suffix */
pub fn get_real_value(v: &Value) -> (r: int)
    requires
        match *v {
            Value::Str(s) => is_valid_numeric_string(s),
            _ => true,
        },
    ensures
        r == value_to_real(*v),
{
    match v {
        Value::Int(i) => *i,
        Value::Real(r) => *r,
        Value::Str(_) => 0,
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
    /* code modified by LLM (iteration 5): no logical changes required; previous error was in helper function. */
    let a_val = get_real_value(&a);
    let b_val = get_real_value(&b);

    if a_val > b_val {
        Some(a)
    } else if b_val > a_val {
        Some(b)
    } else {
        None
    }
}
// </vc-code>


}

fn main() {}