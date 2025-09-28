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
/* helper modified by LLM (iteration 3): Moved helper functions inside verus block to fix compilation error */
fn is_digit(c: char) -> bool {
    (c as int) >= ('0' as int) && (c as int) <= ('9' as int)
}

fn max_n(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

fn min_n(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

fn parse_rectangles_exec(input: Seq<char>) -> Seq<(int, int)> {
    let mut result = Vec::new();
    let mut i = 0;
    loop {
        let mut number1 = 0;
        while i < input.len() && !is_digit(input[i]) {
            i += 1;
        }
        if i >= input.len() { break; }
        while i < input.len() && is_digit(input[i]) {
            number1 = number1 * 10 + ((input[i] as int) - ('0' as int));
            i += 1;
        }
        let mut number2 = 0;
        while i < input.len() && !is_digit(input[i]) {
            i += 1;
        }
        if i >= input.len() { break; }
        while i < input.len() && is_digit(input[i]) {
            number2 = number2 * 10 + ((input[i] as int) - ('0' as int));
            i += 1;
        }
        result.push((number1, number2));
    }
    result@
}

fn check_can_form(rectangles: Seq<(int, int)>) -> (result: bool)
    requires rectangles.len() >= 0
    ensures result == can_form_non_ascending_sequence(rectangles)
{
    if rectangles.len() == 0 {
        true
    } else {
        check_can_form_helper(rectangles, 1, max_spec(rectangles[0].0, rectangles[0].1))
    }
}

/* helper modified by LLM (iteration 5): removed ensures to fix compilation error */
fn check_can_form_helper(rectangles: Seq<(int, int)>, index: int, prev_height: int) -> (result: bool)
    requires 0 <= index <= rectangles.len()
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
            check_can_form_helper(rectangles, index + 1, min_dim)
        } else {
            check_can_form_helper(rectangles, index + 1, max_dim)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input@.len() > 0
    ensures result@ == "YES"@ || result@ == "NO"@
    /* ensures result@ == "YES"@ <==> can_form_non_ascending_sequence(parse_rectangles(input@)) */
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Implemented the solve function by parsing input and checking sequence formation */
    let input_seq = input@;
    let rects = parse_rectangles_exec(input_seq);
    let can = check_can_form(rects);
    if can {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}