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

proof fn value_cmp_reflexive(a: int)
    ensures
        a >= a
{
}

proof fn value_cmp_antisymmetric(a: int, b: int)
    requires
        a >= b,
        b >= a,
    ensures
        a == b
{
}

/* helper modified by LLM (iteration 5): remove requires/ensures from exec function */
spec fn value_to_real_exec(v: Value) -> int {
    match v {
        Value::Int(i) => i,
        Value::Real(r) => r,
        Value::Str(s) => string_to_real(s),
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
    /* code modified by LLM (iteration 5): use pure spec function value_to_real for comparisons */
    let a_real = value_to_real(a);
    let b_real = value_to_real(b);
    
    proof {
        value_cmp_reflexive(a_real);
        value_cmp_reflexive(b_real);
    }
    
    if a_real == b_real {
        Option::None
    } else if a_real > b_real {
        Option::Some(a)
    } else {
        Option::Some(b)
    }
}
// </vc-code>


}

fn main() {}