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
/* helper modified by LLM (iteration 4): Retained a correct helper lemma for reasoning about loop invariants. */
#[verifier::spinoff_prover]
proof fn lemma_integer_values_is_distributive(s1: Seq<Value>, s2: Seq<Value>)
    ensures
        integer_values(s1.add(s2)) == integer_values(s1).add(integer_values(s2)),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_integer_values_is_distributive(s1.subrange(1, s1.len() as int), s2);
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
    /* code modified by LLM (iteration 4): Fixed a compilation error by replacing an invalid method call with a direct cast. */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < values.len()
        invariant
            0 <= i <= values.len(),
            result.len() <= i,
            result@.map(|_idx: int, v: i8| v as int) == integer_values(values@.subrange(0, i as int)),
        decreases values.len() - i
    {
        proof {
            lemma_integer_values_is_distributive(values@.subrange(0, i as int), seq![values@[i as int]]);
        }

        let val = &values[i];
        match val {
            Value::IntVal(x) => {
                let v = *x as i8;
                result.push(v);
            },
            Value::BoolVal(b) => {
                if *b {
                    result.push(1);
                } else {
                    result.push(0);
                }
            },
            _ => {
            },
        }
        i = i + 1;
    }
    result
}

// </vc-code>


}

fn main() {}