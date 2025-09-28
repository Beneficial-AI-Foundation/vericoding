// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn char_to_pos_spec(c: Seq<char>) -> int {
    if c.len() == 1 && c[0] == 'v' { 0 }
    else if c.len() == 1 && c[0] == '>' { 1 }
    else if c.len() == 1 && c[0] == '^' { 2 }
    else if c.len() == 1 && c[0] == '<' { 3 }
    else { 0 }
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == seq!['c', 'w'] || result == seq!['c', 'c', 'w'] || result == seq!['u', 'n', 'd', 'e', 'f', 'i', 'n', 'e', 'd']
}
// </vc-preamble>

// <vc-helpers>
fn char_to_pos(c: char) -> (result: Option<int>)
    ensures
        result.is_none() || result.unwrap() >= 0 && result.unwrap() <= 3,
{
    match c {
        'v' => Some(0),
        '>' => Some(1),
        '^' => Some(2),
        '<' => Some(3),
        _ => None
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures valid_output(result@)
// </vc-spec>
// <vc-code>

    /* code modified by LLM (iteration 5): Fixed number literal suffixes and type mismatches for nat */
    let s = input@;
    if s.len() <= 1nat {
        return "undefined".to_string();
    }
    let mut i: nat = 0nat;
    let mut all_clockwise = true;
    let mut all_counterclockwise = true;
    while i < nat(s.len()) - 1nat
        invariant
            i <= nat(s.len()) - 1nat,
            all_clockwise || all_counterclockwise || (!all_clockwise && !all_counterclockwise),
        decreases
            nat(s.len()) - i
    {
        let opt_pos1 = char_to_pos(s@[i]);
        let opt_pos2 = char_to_pos(s@[i + 1nat]);
        if let Some(pos1) = opt_pos1 {
            if let Some(pos2) = opt_pos2 {
                let diff = pos2 - pos1;
                let mut turn = diff % 4;
                if turn < 0 {
                    turn = turn + 4;
                }
                if turn == 1 {
                    all_counterclockwise = false;
                } else if turn == 3 {
                    all_clockwise = false;
                } else {
                    all_clockwise = false;
                    all_counterclockwise = false;
                }
            } else {
                all_clockwise = false;
                all_counterclockwise = false;
            }
        } else {
            all_clockwise = false;
            all_counterclockwise = false;
        }
        i = i + 1nat;
    }
    if !all_clockwise && !all_counterclockwise {
        "undefined".to_string()
    } else if all_clockwise {
        "cw".to_string()
    } else {
        "ccw".to_string()
    }

// </vc-code>


}

fn main() {}