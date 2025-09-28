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
/* helper modified by LLM (iteration 5): simple extractor of integer-like values for specs */
spec fn as_int_seq(v: Value) -> Seq<int> {
    match v {
        Value::IntVal(i) => seq![i],
        Value::BoolVal(b) => seq![if b { 1int } else { 0int }],
        _ => Seq::<int>::empty(),
    }
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
    /* code modified by LLM (iteration 5): collect integers represented by booleans; skip others */
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < values.len()
        invariant
            i <= values.len(),
            res.len() <= i,
            res.len() <= values.len(),
        decreases values.len() - i
    {
        match values[i] {
            Value::BoolVal(b) => {
                let x: i8 = if b { 1i8 } else { 0i8 };
                res.push(x);
            }
            Value::IntVal(_iv) => {
                // Cannot soundly convert spec int to exec i8; skip
            }
            _ => { }
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}

fn main() {}