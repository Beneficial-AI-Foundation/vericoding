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
/* helper modified by LLM (iteration 5): fixed return type for string_to_real_exec */
exec fn value_to_real_exec(v: Value) -> int
    ensures
        value_to_real(v) == value_to_real_exec(v),
{
    match v {
        Value::Int(i) => i,
        Value::Real(r) => r,
        Value::Str(s) => string_to_real_exec(s),
    }
}

/* helper modified by LLM (iteration 5): fixed return type for string_to_real_exec */
exec fn string_to_real_exec(s: String) -> int
    ensures
        string_to_real(s) == string_to_real_exec(s),
{
    0int
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
    /* code modified by LLM (iteration 5): use exec mode helpers instead of spec functions */
    let a_real = value_to_real_exec(a);
    let b_real = value_to_real_exec(b);
    
    if a_real > b_real {
        Some(a)
    } else if b_real > a_real {
        Some(b)
    } else {
        None
    }
}
// </vc-code>


}

fn main() {}