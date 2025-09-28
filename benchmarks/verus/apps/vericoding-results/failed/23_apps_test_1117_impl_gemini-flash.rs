// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn can_form_non_ascending_sequence(rectangles: Seq<(int, int)>) -> bool {
    if rectangles.len() <= 1 {
        true
    } else {
        can_form_non_ascending_sequence_helper(rectangles, 1, max_spec(rectangles[0].0, rectangles[0].1))
    }
}

spec fn can_form_non_ascending_sequence_helper(rectangles: Seq<(int, int)>, index: int, prev_height: int) -> bool
    recommends 0 <= index <= rectangles.len()
    decreases rectangles.len() - index
{
    if index >= rectangles.len() {
        true
    } else {
        let a = rectangles[index].0;
        let b = rectangles[index].1;
        let min_dim = min_spec(a, b);
        let max_dim = max_spec(a, b);

        if min_dim > prev_height {
            false
        } else if min_dim <= prev_height < max_dim {
            can_form_non_ascending_sequence_helper(rectangles, index + 1, min_dim)
        } else {
            can_form_non_ascending_sequence_helper(rectangles, index + 1, max_dim)
        }
    }
}

spec fn parse_rectangles(input: Seq<char>) -> Seq<(int, int)> {
    /* Placeholder for parsing logic */
    seq![]
}

spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn max_spec(a: int, b: int) -> int {
    if a >= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add parse_rectangles_from_string function */
payspec fn parse_rectangles_from_string(input: &str) -> (rectangles: Seq<(int, int)>)
{
    let mut result = Seq::empty();
    let mut chars = input.chars();
    let mut current_num = 0;
    let mut first_num_in_pair = true;
    let mut a = 0;

    while let Some(c) = chars.next() {
        if c >= '0' && c <= '9' {
            current_num = current_num * 10 + (c as int - '0' as int);
        } else if c == 'x' || c == 'X' {
            a = current_num;
            current_num = 0;
            first_num_in_pair = false;
        } else if c == ' ' || c == '\n' || c == '\r' {
            if !first_num_in_pair {
                result = result.push((a, current_num));
                current_num = 0;
                first_num_in_pair = true;
            }
        } else {
            // Handle other characters if necessary or ignore
        }
    }

    // Handle the last rectangle if the string doesn't end with a space/newline
    if !first_num_in_pair {
        result = result.push((a, current_num));
    }
    result
}

proof fn lemma_min_max_dims(a: int, b: int)
    ensures min_spec(a, b) <= max_spec(a, b)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input@.len() > 0
    ensures result@ == "YES"@ || result@ == "NO"@
    /* ensures result@ == "YES"@ <==> can_form_non_ascending_sequence(parse_rectangles(input@)) */
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced parse_rectangles with parse_rectangles_from_string */
{
    let rectangles = parse_rectangles_from_string(input);

    if can_form_non_ascending_sequence(rectangles) {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}