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
fn convert_int_to_i8(i: int) -> (result: i8)
    requires
        -128 <= i <= 127,
    ensures
        result as int == i,
{
    /* helper modified by LLM (iteration 5): replaced to_i8() with explicit cast */
    i as i8
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
{
    /* code modified by LLM (iteration 5): updated to use fixed helper */
    let mut result = Vec::new();
    for value in values {
        match value {
            Value::IntVal(i) => {
                proof {
                    assert(-128 <= i && i <= 127);
                }
                result.push(convert_int_to_i8(i));
            },
            Value::BoolVal(b) => result.push(if b { 1i8 } else { 0i8 }),
            _ => (),
        }
    }
    result
}
// </vc-code>


}

fn main() {}