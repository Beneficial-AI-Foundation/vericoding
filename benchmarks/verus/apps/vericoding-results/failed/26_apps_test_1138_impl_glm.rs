// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D'
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    count_char_helper(s, c, 0, 0)
}

spec fn count_char_helper(s: Seq<char>, c: char, index: int, count: int) -> int
    decreases s.len() - index
{
    if index >= s.len() {
        count
    } else if s.index(index) == c {
        count_char_helper(s, c, index + 1, count + 1)
    } else {
        count_char_helper(s, c, index + 1, count)
    }
}

spec fn count_char_from_index(s: Seq<char>, c: char, index: int) -> int
    decreases s.len() - index
{
    if index >= s.len() {
        0
    } else if s.index(index) == c {
        1 + count_char_from_index(s, c, index + 1)
    } else {
        count_char_from_index(s, c, index + 1)
    }
}

spec fn correct_result(s: Seq<char>, result: int) -> bool {
    (s.len() % 2 != 0 ==> result == -1) &&
    (s.len() % 2 == 0 ==> result >= 0) &&
    (s.len() % 2 == 0 ==> result <= s.len() / 2) &&
    (s.len() % 2 == 0 ==> result == (abs(count_char(s, 'L') - count_char(s, 'R')) + abs(count_char(s, 'U') - count_char(s, 'D'))) / 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added is_even_length helper */
fn is_even_length(s: Seq<char>) -> bool {
    s.len() % 2 == 0
}

/* helper modified by LLM (iteration 4): added calculate_min_moves helper */
fn calculate_min_moves(s: Seq<char>) -> (result: int)
    ensures 0 <= result <= s.len() / 2
{
    let count_l = count_char(s, 'L');
    let count_r = count_char(s, 'R');
    let count_u = count_char(s, 'U');
    let count_d = count_char(s, 'D');
    let diff_lr = abs(count_l - count_r);
    let diff_ud = abs(count_u - count_d);
    (diff_lr + diff_ud) / 2
}

/* helper modified by LLM (iteration 5): added int_to_i8 helper for safe conversion */
fn int_to_i8(x: int) -> (y: i8)
    ensures y as int == x
    recommends -128 <= x <= 127
{
    proof {
        assert(-128 <= x <= 127);
    }
    x as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures correct_result(s@, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation by using int_to_i8 helper) */
{
    if is_even_length(s@) {
        let min_moves = calculate_min_moves(s@);
        assert(min_moves <= 127);
        int_to_i8(min_moves)
    } else {
        int_to_i8(-1)
    }
}
// </vc-code>


}

fn main() {}