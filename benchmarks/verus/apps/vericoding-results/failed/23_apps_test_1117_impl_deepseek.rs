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
/* helper modified by LLM (iteration 5): Fix type mismatch in recursive calls by casting index+1 to usize */
proof fn can_form_non_ascending_sequence_impl_helper(rectangles: &Vec<(int, int)>, index: usize, prev_height: int) -> (result: bool)
    requires 0 <= index <= rectangles@.len()
    ensures result == can_form_non_ascending_sequence_helper(rectangles@, index as int, prev_height)
    decreases rectangles@.len() - index as int
{
    if index >= rectangles.len() {
        true
    } else {
        match rectangles.get(index) {
            Some(&(a, b)) => {
                let min_dim = min_spec(a, b);
                let max_dim = max_spec(a, b);
                
                if min_dim > prev_height {
                    false
                } else if min_dim <= prev_height && prev_height < max_dim {
                    can_form_non_ascending_sequence_impl_helper(rectangles, (index + 1) as usize, min_dim)
                } else {
                    can_form_non_ascending_sequence_impl_helper(rectangles, (index + 1) as usize, max_dim)
                }
            }
            None => true,
        }
    }
}

spec fn parse_rectangles_impl(input: &str) -> (result: Vec<(int, int)>)
    ensures result@ == parse_rectangles(input@)
{
    let mut rectangles: Vec<(int, int)> = Vec::new();
    let mut lines = input.split('\n');
    
    // Skip first line with number of rectangles
    let _count_line = lines.next();
    
    while let Some(line) = lines.next()
        invariant
            rectangles@.len() <= input@.len() / 2 + 1,
            forall|i: int| 0 <= i < rectangles@.len() ==> 
                rectangles@[i].0 > 0 && rectangles@[i].1 > 0,
            rectangles@ == parse_rectangles(Seq::empty())
    {
        if line.len() == 0 {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 2 {
            let width = parts[0].parse::<i32>().unwrap() as int;
            let height = parts[1].parse::<i32>().unwrap() as int;
            rectangles.push((width, height));
        }
    }
    rectangles
}

fn min_spec_fun(a: int, b: int) -> (result: int)
    ensures result == min_spec(a, b)
{
    if a <= b { a } else { b }
}

fn max_spec_fun(a: int, b: int) -> (result: int)
    ensures result == max_spec(a, b)
{
    if a >= b { a } else { b }
}

fn can_form_non_ascending_sequence_impl(rectangles: &Vec<(int, int)>) -> (result: bool)
    ensures result == can_form_non_ascending_sequence(rectangles@)
{
    if rectangles.len() <= 1 {
        return true;
    }
    
    match rectangles.get(0) {
        Some(&(width0, height0)) => {
            let mut current_height = max_spec_fun(width0, height0);
            let mut i: usize = 1;
            
            while i < rectangles.len()
                invariant
                    0 < i <= rectangles@.len(),
                    current_height >= 0,
                    can_form_non_ascending_sequence_helper(rectangles@, i as int, current_height) == 
                        can_form_non_ascending_sequence_impl_helper(rectangles, i, current_height)
                decreases rectangles@.len() - i as int
            {
                match rectangles.get(i) {
                    Some(&(width, height)) => {
                        let min_dim = min_spec_fun(width, height);
                        let max_dim = max_spec_fun(width, height);
                        
                        if min_dim > current_height {
                            return false;
                        } else if min_dim <= current_height && current_height < max_dim {
                            current_height = min_dim;
                        } else {
                            current_height = max_dim;
                        }
                        
                        i += 1;
                    }
                    None => break,
                }
            }
            
            true
        }
        None => true,
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
/* code modified by LLM (iteration 5): Use proper function calls */
{
    let rectangles = parse_rectangles_impl(input);
    
    if can_form_non_ascending_sequence_impl(&rectangles) {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}