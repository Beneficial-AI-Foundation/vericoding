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
/* helper modified by LLM (iteration 3): string_to_real_exec */
fn string_to_real_exec(s: String) -> int {
    0.into()
}

/* helper modified by LLM (iteration 3): string_to_real_spec_exec_rel */
proof fn string_to_real_spec_exec_rel(s: String)
    requires
        is_valid_numeric_string(s),
    ensures
        string_to_real(s) == string_to_real_exec(s),
{
    proof {
        assert(string_to_real(s) == 0);
        assert(string_to_real_exec(s) == 0.into());
        assert(0 == 0.into());
    }
}

/* helper modified by LLM (iteration 3): value_to_real_exec */
fn value_to_real_exec(v: Value) -> int {
    match v {
        Value::Int(i) => i,
        Value::Real(r) => r,
        Value::Str(s) => string_to_real_exec(s),
    }
}

/* helper modified by LLM (iteration 3): value_to_real_spec_exec_rel */
proof fn value_to_real_spec_exec_rel(v: Value)
    requires
        matches!(v, Value::Str(_)) ==> is_valid_numeric_string(v.arrow_Str_0()),
    ensures
        value_to_real(v) == value_to_real_exec(v),
{
    proof {
        match v {
            Value::Int(i) => {
                assert(value_to_real(v) == i);
                assert(value_to_real_exec(v) == i);
            }
            Value::Real(r) => {
                assert(value_to_real(v) == r);
                assert(value_to_real_exec(v) == r);
            }
            Value::Str(s) => {
                string_to_real_spec_exec_rel(s);
                assert(value_to_real(v) == string_to_real(s));
                assert(value_to_real_exec(v) == string_to_real_exec(s));
            }
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
    /* code modified by LLM (iteration 3): compare_one implementation using exec helpers */
    let ra = value_to_real_exec(a);
    let rb = value_to_real_exec(b);

    proof {
        value_to_real_spec_exec_rel(a);
        value_to_real_spec_exec_rel(b);
    }

    let result = if ra == rb {
        None::<Value>
    } else if ra > rb {
        Some(a)
    } else {
        Some(b)
    };

    proof {
        assert(value_to_real(a) == ra);
        assert(value_to_real(b) == rb);

        if ra == rb {
            assert(value_to_real(a) == value_to_real(b));
            assert(matches!(result, Option::None));
        } else if ra > rb {
            assert(value_to_real(a) > value_to_real(b));
            assert(result == Some(a));
        } else {
            assert(value_to_real(b) > value_to_real(a));
            assert(result == Some(b));
        }

        if matches!(result, Option::Some(_)) {
            match result {
                Some(v) => {
                    assert(v == a || v == b);
                }
                None => {}
            }
        }
    }

    result
}
// </vc-code>


}

fn main() {}