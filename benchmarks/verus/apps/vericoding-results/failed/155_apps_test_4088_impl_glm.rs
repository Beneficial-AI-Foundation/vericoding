// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input_format(input: Seq<char>) -> bool {
    input.len() > 0
    /* TODO: Implement full validation logic for:
     * - Lines parsing and validation
     * - Test case count validation  
     * - String and integer array parsing
     * - Character and bounds validation
     */
}

spec fn valid_output_format(output: Seq<char>, input: Seq<char>) -> bool {
    valid_input_format(input) ==> output.len() > 0
    /* TODO: Implement validation for:
     * - Output lines matching test cases
     * - Correct string lengths
     * - Valid lowercase characters
     */
}

spec fn output_satisfies_constraints(output: Seq<char>, input: Seq<char>) -> bool {
    valid_input_format(input) ==> true
    /* TODO: Implement constraint validation for:
     * - Distance sum calculations
     * - Character ordering requirements
     */
}

spec fn preserves_character_usage(output: Seq<char>, input: Seq<char>) -> bool {
    valid_input_format(input) ==> true
    /* TODO: Implement character count preservation:
     * - Character frequency validation
     * - Subset usage validation
     */
}

spec fn contains_newline_terminated_results(output: Seq<char>) -> bool {
    output.len() > 0 ==> output[output.len() - 1] == '\n'
}

spec fn sum_distances_to_greater_chars(t: Seq<char>, j: int) -> int {
    0
    /* TODO: Implement distance sum calculation:
     * - Compare characters lexicographically
     * - Calculate absolute differences
     * - Sum all applicable distances
     */
}

spec fn abs_diff(i: int, j: int) -> int {
    if i >= j { i - j } else { j - i }
}
// </vc-preamble>

// <vc-helpers>
fn sort_string(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
{
    let mut chars: Vec<char> = s.chars().collect();
    chars.sort();
    chars.into_iter().collect()
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires 
        stdin_input@.len() > 0,
        valid_input_format(stdin_input@),
    ensures 
        valid_output_format(result@, stdin_input@),
        output_satisfies_constraints(result@, stdin_input@),
        preserves_character_usage(result@, stdin_input@),
        result@.len() > 0 ==> contains_newline_terminated_results(result@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed for-loop range from inclusive to exclusive */
    let lines: Vec<&str> = stdin_input.lines().collect();
    let t = lines[0].parse::<usize>().unwrap();
    let mut result = String::new();
    for i in 1..(t+1) {
        let s = lines[i];
        let sorted = sort_string(s);
        result.push_str(&sorted);
        result.push('\n');
    }
    result
}
// </vc-code>


}

fn main() {}