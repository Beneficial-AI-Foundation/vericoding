// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum Value {
    IntVal(int),
    BoolVal(bool),
    StringVal(Seq<char>),
    RealVal(int), /* using int for real approximation */
    OtherVal,
}

spec fn valid_input(values: Seq<Value>) -> bool {
    true  /* All sequences of Value are valid input */
}

spec fn integer_values(values: Seq<Value>) -> Seq<int> 
    decreases values.len()
{
    if values.len() == 0 {
        Seq::<int>::empty()
    } else {
        match values.index(0) {
            Value::IntVal(i) => seq![i].add(integer_values(values.subrange(1, values.len() as int))),
            Value::BoolVal(b) => seq![if b { 1int } else { 0int }].add(integer_values(values.subrange(1, values.len() as int))),
            _ => integer_values(values.subrange(1, values.len() as int))
        }
    }
}

spec fn valid_output(input: Seq<Value>, output: Seq<int>) -> bool {
    output == integer_values(input)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix compilation errors in filter function signatures and type casts */

spec fn is_int_value(value: Value) -> bool {
    match value {
        Value::IntVal(_) | Value::BoolVal(_) => true,
        _ => false
    }
}

spec fn integer_value(value: Value) -> int {
    match value {
        Value::IntVal(i) => i,
        Value::BoolVal(b) => if b { 1 } else { 0 },
        _ => 0
    }
}

proof fn filter_integers_loop_invariant_maintained(values: Seq<Value>, index: nat, result: Seq<int>)
    requires
        index < values.len(),
        result == integer_values(values.subrange(0, index as int)),
    ensures
        if is_int_value(values[index]) {
            result.push(integer_value(values[index])) == integer_values(values.subrange(0, (index + 1) as int))
        } else {
            result == integer_values(values.subrange(0, (index + 1) as int))
        }
{
}

proof fn filter_integers_postcondition(values: Seq<Value>, result: Seq<int>)
    requires
        result == integer_values(values),
    ensures
        valid_output(values, result)
{
}
// </vc-helpers>

// <vc-spec>
fn filter_integers(values: Vec<Value>) -> (result: Vec<i8>)
    requires
        valid_input(values@),
    ensures
        valid_output(values@, result@.map(|i: int, v: i8| v as int)),
        result.len() <= values.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fix compilation errors in filter call and indexing */
{
    let mut index: usize = 0;
    let mut result_vec = Vec::new();
    
    while index < values.len()
        invariant
            index <= values.len(),
            result_vec@ == integer_values(values@.subrange(0, index as int))
        decreases values.len() - index
    {
        let value = values[index];
        match value {
            Value::IntVal(i) => {
                result_vec.push(i as i8);
            },
            Value::BoolVal(b) => {
                result_vec.push(if b { 1i8 } else { 0i8 });
            },
            _ => {}
        }
        proof {
            filter_integers_loop_invariant_maintained(values@, index, result_vec@);
        }
        index += 1;
    }
    
    proof {
        filter_integers_postcondition(values@, result_vec@);
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}