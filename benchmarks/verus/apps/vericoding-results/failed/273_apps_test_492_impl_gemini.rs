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
/* helper modified by LLM (iteration 2): [changed return type to u32 for compilation] */
fn char_to_pos(c: char) -> (pos: u32)
    requires
        c == 'v' || c == '>' || c == '^' || c == '<',
    ensures
        c == 'v' ==> pos == 0,
        c == '>' ==> pos == 1,
        c == '^' ==> pos == 2,
        c == '<' ==> pos == 3,
        char_to_pos_spec(seq![c]) == pos as int,
{
    if c == 'v' { 0u32 }
    else if c == '>' { 1u32 }
    else if c == '^' { 2u32 }
    else { 3u32 }
}

/* helper modified by LLM (iteration 3): [Replaced unsupported is_ascii_digit with a spec-compatible range check] */
fn char_to_digit(c: char) -> (d: u32)
    requires
        '0' <= c && c <= '9',
    ensures
        d as int == (c as nat) - ('0' as nat),
        0 <= d <= 9,
{
    c as u32 - '0' as u32
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures valid_output(result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed compilation errors by using sequence indexing s@[] and nat literal.] */
{
    let s = input@;
    if s.len() != 5nat {
        return "undefined".to_string();
    }

    let c1 = s@[0];
    let space1 = s@[1];
    let c2 = s@[2];
    let space2 = s@[3];
    let n_char = s@[4];

    if space1 != ' ' || space2 != ' ' {
        return "undefined".to_string();
    }

    let is_c1_valid = c1 == 'v' || c1 == '>' || c1 == '^' || c1 == '<';
    let is_c2_valid = c2 == 'v' || c2 == '>' || c2 == '^' || c2 == '<';

    if !is_c1_valid || !is_c2_valid || !('0' <= n_char && n_char <= '9') {
        return "undefined".to_string();
    }

    let p1 = char_to_pos(c1);
    let p2 = char_to_pos(c2);
    let n = char_to_digit(n_char);

    let is_cw = (p1 + n) % 4 == p2;
    let is_ccw = (p1 + 3 * n) % 4 == p2;

    if is_cw && !is_ccw {
        "cw".to_string()
    } else if !is_cw && is_ccw {
        "ccw".to_string()
    } else {
        "undefined".to_string()
    }
}
// </vc-code>


}

fn main() {}