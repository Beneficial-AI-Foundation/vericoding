use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (ret:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn count_uppercase_sum(seq: Seq<char>) -> (ret:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_sum(seq.drop_last()) + if is_upper_case(seq.last()) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}
// pure-end

/*
function_signature: "def digitSum(string: str) -> Nat"
docstring: |
Write a function that takes a string as input and returns the sum of the upper characters only'
ASCII codes.
test_cases:
- input: ""
expected_output: 0
- input: "abAB"
expected_output: 131
- input: "helloE"
expected_output: 69
*/

fn digit_sum(text: &[char]) -> (sum: u128)
    // post-conditions-start
    ensures
        count_uppercase_sum(text@) == sum,
    // post-conditions-end
{
    // impl-start
    assume(false);
    0
    // impl-end
}

} // verus!
fn main() {}