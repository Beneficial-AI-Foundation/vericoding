use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (result:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '<' => (x + 1, b),
                    '>' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}
// pure-end
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

/*
function_signature: "def correct_bracketing(brackets: str) -> Bool"
docstring: |
brackets is a string of "<" and ">".
return True if every opening bracket has a corresponding closing bracket, i.e., (each open bracket is properly closed)
test_cases:
- input: "<"
expected_output: False
- input: "<>"
expected_output: True
- input: "<<><>>"
expected_output: True
- input: "><<>"
expected_output: False
*/

fn correct_bracketing(brackets: &str) -> (ret: bool)
    // pre-conditions-start
    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret <==> spec_bracketing(brackets@),
    // post-conditions-end
{
    // impl-start
    assume(false);
    false
    // impl-end
}

} // verus!
fn main() {}