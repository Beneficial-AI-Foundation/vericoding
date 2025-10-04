// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn eval_rpn(tokens: Seq<String>) -> int
{
    0
}

fn eval_rpn_exec(tokens: Vec<String>) -> (result: i32)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview */
/* Assurance level: guarded */

proof fn eval_rpn_empty()
    ensures eval_rpn(seq![]) == 0
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_single_positive()
    ensures eval_rpn(seq!["5".to_string()]) == 5
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_single_negative()
    ensures eval_rpn(seq!["-5".to_string()]) == -5
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_addition()
    ensures eval_rpn(seq!["3".to_string(), "2".to_string(), "+".to_string()]) == 5
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_subtraction()
    ensures eval_rpn(seq!["3".to_string(), "2".to_string(), "-".to_string()]) == 1
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_multiplication()
    ensures eval_rpn(seq!["3".to_string(), "2".to_string(), "*".to_string()]) == 6
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_division()
    ensures eval_rpn(seq!["6".to_string(), "2".to_string(), "/".to_string()]) == 3
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_negative_division_1()
    ensures eval_rpn(seq!["6".to_string(), "-2".to_string(), "/".to_string()]) == -3
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_negative_division_2()
    ensures eval_rpn(seq!["-6".to_string(), "2".to_string(), "/".to_string()]) == -3
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_negative_multiplication()
    ensures eval_rpn(seq!["-2".to_string(), "-3".to_string(), "*".to_string()]) == 6
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_negative_addition()
    ensures eval_rpn(seq!["-1".to_string(), "1".to_string(), "+".to_string()]) == 0
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_complex_1()
    ensures eval_rpn(seq!["2".to_string(), "1".to_string(), "+".to_string(), "3".to_string(), "*".to_string()]) == 9
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn eval_rpn_complex_2()
    ensures eval_rpn(seq!["4".to_string(), "13".to_string(), "5".to_string(), "/".to_string(), "+".to_string()]) == 6
{
    assume(false); // TODO: Remove this line and implement the proof
}

}

fn main() {
    // println!("{}", eval_rpn_exec(vec!["2".to_string(), "1".to_string(), "+".to_string(), "3".to_string(), "*".to_string()]));
    // println!("{}", eval_rpn_exec(vec!["4".to_string(), "13".to_string(), "5".to_string(), "/".to_string(), "+".to_string()]));
    // println!("{}", eval_rpn_exec(vec!["10".to_string(), "6".to_string(), "9".to_string(), "3".to_string(), "+".to_string(), "-11".to_string(), "*".to_string(), "/".to_string(), "*".to_string(), "17".to_string(), "+".to_string(), "5".to_string(), "+".to_string()]));
}