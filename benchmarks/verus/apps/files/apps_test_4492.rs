// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Helper spec functions for string parsing */
spec fn split_by_newline_spec(s: &str) -> Seq<&str> { Seq::empty() }
spec fn split_by_space_spec(s: &str) -> Seq<&str> { Seq::empty() }
spec fn parse_int_spec(s: &str) -> int { 0 }
spec fn int_to_string_spec(n: int) -> Seq<char> { Seq::empty() }
spec fn string_len_spec(s: &str) -> nat { 0 }
spec fn string_result_len_spec(s: String) -> nat { 0 }

spec fn valid_input(input: &str) -> bool {
    let lines = split_by_newline_spec(input);
    lines.len() >= 2 &&
    {
        let first_line = split_by_space_spec(lines[0]);
        first_line.len() >= 2 &&
        {
            let n = parse_int_spec(first_line[0]);
            let x = parse_int_spec(first_line[1]);
            n >= 2 && x >= 0 &&
            {
                let second_line = split_by_space_spec(lines[1]);
                second_line.len() == n &&
                forall|i: int| 0 <= i < n ==> parse_int_spec(second_line[i]) >= 0
            }
        }
    }
}

spec fn minimum_candies_needed(input: &str) -> int
    recommends valid_input(input)
{
    let lines = split_by_newline_spec(input);
    let first_line = split_by_space_spec(lines[0]);
    let n = parse_int_spec(first_line[0]);
    let x = parse_int_spec(first_line[1]);
    let second_line = split_by_space_spec(lines[1]);
    let a = Seq::new(n as nat, |i: int| parse_int_spec(second_line[i]));
    compute_minimum_operations(a, x)
}

spec fn compute_minimum_operations(a: Seq<int>, x: int) -> int
    recommends a.len() >= 2 && x >= 0 && forall|i: int| 0 <= i < a.len() ==> a[i] >= 0
{
    let a0 = if a[0] > x { x } else { a[0] };
    let cnt0 = if a[0] > x { a[0] - x } else { 0 };
    let new_a = a.update(0, a0);
    compute_operations_from_index(a, x, 1, new_a, cnt0)
}

spec fn compute_operations_from_index(original_a: Seq<int>, x: int, index: int, current_a: Seq<int>, current_count: int) -> int
    recommends 
        original_a.len() >= 2 &&
        x >= 0 &&
        1 <= index <= original_a.len() &&
        current_a.len() == original_a.len() &&
        current_count >= 0 &&
        forall|i: int| 0 <= i < original_a.len() ==> original_a[i] >= 0
    decreases original_a.len() - index
{
    if index >= original_a.len() {
        current_count
    } else {
        let new_value = if current_a[index] + current_a[index - 1] > x {
            x - current_a[index - 1]
        } else {
            current_a[index]
        };
        let additional_ops = if current_a[index] + current_a[index - 1] > x {
            current_a[index] + current_a[index - 1] - x
        } else {
            0
        };
        let new_a = current_a.update(index, new_value);
        compute_operations_from_index(original_a, x, index + 1, new_a, current_count + additional_ops)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires 
        string_len_spec(input) > 0,
        valid_input(input),
    ensures 
        string_result_len_spec(result) > 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}