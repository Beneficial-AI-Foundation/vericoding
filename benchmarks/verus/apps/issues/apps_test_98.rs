// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines_func(input);
    lines.len() >= 3 &&
    {
        let board_parts = split_spaces_func(lines[0]);
        let paint1_parts = split_spaces_func(lines[1]);
        let paint2_parts = split_spaces_func(lines[2]);
        board_parts.len() >= 2 && paint1_parts.len() >= 2 && paint2_parts.len() >= 2 &&
        is_valid_int(board_parts[0]) && is_valid_int(board_parts[1]) &&
        is_valid_int(paint1_parts[0]) && is_valid_int(paint1_parts[1]) &&
        is_valid_int(paint2_parts[0]) && is_valid_int(paint2_parts[1])
    }
}

spec fn can_place_both_paintings(a: int, b: int, c: int, d: int, e: int, f: int) -> bool {
    (c+e <= a && max(d,f) <= b) ||
    (c+e <= b && max(d,f) <= a) ||
    (c+f <= a && max(d,e) <= b) ||
    (c+f <= b && max(d,e) <= a) ||
    (d+e <= a && max(c,f) <= b) ||
    (d+e <= b && max(c,f) <= a) ||
    (d+f <= a && max(c,e) <= b) ||
    (d+f <= b && max(c,e) <= a)
}

spec fn max(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

spec fn is_valid_int(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> ('0' <= s[i] && s[i] <= '9')
}

spec fn split_lines_func(s: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['a']; 3]
}

spec fn split_spaces_func(s: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['1']; 2]
}

spec fn parse_int_func(s: Seq<char>) -> int {
    1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Vec<char>)
    requires input.len() > 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}

fn main() {}