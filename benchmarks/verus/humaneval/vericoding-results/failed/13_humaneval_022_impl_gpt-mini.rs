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
/* helper modified by LLM (iteration 5): lemma linking integer_values for prefix step */
lemma integer_values_prefix_step(values: Seq<Value>, i: int)
    requires
        0 <= i && i < values.len(),
    ensures
        integer_values(values.subrange(0, i + 1)) ==
            match values.index(i) {
                Value::IntVal(n) => seq![n].add(integer_values(values.subrange(i + 1, values.len()))),
                Value::BoolVal(b) => seq![if b { 1int } else { 0int }].add(integer_values(values.subrange(i + 1, values.len()))),
                _ => integer_values(values.subrange(i + 1, values.len())),
            },
{
    proof {
        // Unfolding integer_values on the prefix gives the desired equality
        reveal(integer_values);
        assert(integer_values(values.subrange(0, i + 1)) == integer_values(values.subrange(0, i + 1)));
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
    /* code modified by LLM (iteration 5): iterate values and maintain relation to integer_values */
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < values.len()
        invariant
            res.len() <= i,
            res@.map(|j: int, v: i8| v as int) == integer_values(values@.subrange(0, i as int)),
        decreases values.len() - i
    {
        match &values[i] {
            Value::IntVal(n) => {
                res.push((*n) as i8);
                proof {
                    // show invariant holds at i+1 using the prefix lemma
                    integer_values_prefix_step(values@, i as int);
                    assert(res@.map(|j: int, v: i8| v as int) == integer_values(values@.subrange(0, i as int + 1)));
                }
            }
            Value::BoolVal(b) => {
                res.push(if *b { 1i8 } else { 0i8 });
                proof {
                    integer_values_prefix_step(values@, i as int);
                    assert(res@.map(|j: int, v: i8| v as int) == integer_values(values@.subrange(0, i as int + 1)));
                }
            }
            _ => {
                proof {
                    // no push, but the prefix of values of length i+1 may not add an element
                    integer_values_prefix_step(values@, i as int);
                    assert(res@.map(|j: int, v: i8| v as int) == integer_values(values@.subrange(0, i as int + 1)));
                }
            }
        }
        i = i + 1;
    }
    res
}

// </vc-code>


}

fn main() {}