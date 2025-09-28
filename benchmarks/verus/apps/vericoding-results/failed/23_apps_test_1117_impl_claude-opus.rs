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
/* helper modified by LLM (iteration 5): Fixed map closure type annotation */
fn min(a: i32, b: i32) -> (result: i32)
    ensures result == min_spec(a as int, b as int)
{
    if a <= b { a } else { b }
}

fn max(a: i32, b: i32) -> (result: i32)
    ensures result == max_spec(a as int, b as int)
{
    if a >= b { a } else { b }
}

fn can_form_helper(rectangles: &Vec<(i32, i32)>, index: usize, prev_height: i32) -> (result: bool)
    requires
        index <= rectangles.len(),
        index > 0,
    ensures
        result == can_form_non_ascending_sequence_helper(rectangles@.map(|p: (i32, i32)| (p.0 as int, p.1 as int)), index as int, prev_height as int),
    decreases rectangles.len() - index
{
    if index >= rectangles.len() {
        return true;
    }
    
    let a = rectangles[index].0;
    let b = rectangles[index].1;
    let min_dim = min(a, b);
    let max_dim = max(a, b);
    
    if min_dim > prev_height {
        false
    } else if min_dim <= prev_height && prev_height < max_dim {
        can_form_helper(rectangles, index + 1, min_dim)
    } else {
        can_form_helper(rectangles, index + 1, max_dim)
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
    /* code modified by LLM (iteration 5): No changes to main code */
    let mut rectangles: Vec<(i32, i32)> = Vec::new();
    let input_bytes = input.as_bytes();
    let mut i: usize = 0;
    
    while i < input_bytes.len()
        invariant
            i <= input_bytes.len(),
    {
        if i + 1 < input_bytes.len() && input_bytes[i] >= b'0' && input_bytes[i] <= b'9' && input_bytes[i+1] >= b'0' && input_bytes[i+1] <= b'9' {
            let a = (input_bytes[i] - b'0') as i32;
            let b = (input_bytes[i+1] - b'0') as i32;
            rectangles.push((a, b));
            i = i + 2;
            
            while i < input_bytes.len() && (input_bytes[i] == b' ' || input_bytes[i] == b'\n')
                invariant
                    i <= input_bytes.len(),
            {
                i = i + 1;
            }
        } else {
            i = i + 1;
        }
    }
    
    if rectangles.len() == 0 {
        return "NO".to_string();
    }
    
    if rectangles.len() == 1 {
        return "YES".to_string();
    }
    
    let first_a = rectangles[0].0;
    let first_b = rectangles[0].1;
    let initial_height = max(first_a, first_b);
    
    let result = can_form_helper(&rectangles, 1, initial_height);
    
    if result {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}