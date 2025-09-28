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
/* helper modified by LLM (iteration 5): fixed integer literal type annotations */
proof fn count_char_equiv(s: Seq<char>, c: char)
    ensures count_char(s, c) == count_char_from_index(s, c, 0)
{
    count_char_helper_equiv(s, c, 0, 0);
}

proof fn count_char_helper_equiv(s: Seq<char>, c: char, index: int, count: int)
    requires index >= 0
    ensures count_char_helper(s, c, index, count) == count + count_char_from_index(s, c, index)
    decreases s.len() - index
{
    if index >= s.len() {
    } else if s.index(index) == c {
        count_char_helper_equiv(s, c, index + 1, count + 1);
    } else {
        count_char_helper_equiv(s, c, index + 1, count);
    }
}

proof fn count_char_additive(s: Seq<char>, c: char, i: int)
    requires 0 <= i < s.len()
    ensures count_char_from_index(s, c, 0) == count_char_from_index(s, c, 1) + (if s.index(0) == c { 1int } else { 0int })
{
}

proof fn count_char_shift(s: Seq<char>, c: char, i: int)
    requires 0 <= i < s.len()
    ensures count_char_from_index(s, c, i) == (if s.index(i) == c { 1int } else { 0int }) + count_char_from_index(s, c, i + 1)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures correct_result(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversion from usize to int */
    if s.len() % 2 != 0 {
        return -1;
    }
    
    let mut count_l = 0;
    let mut count_r = 0;
    let mut count_u = 0;
    let mut count_d = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count_l == count_char_from_index(s@, 'L', 0) - count_char_from_index(s@, 'L', i as int),
            count_r == count_char_from_index(s@, 'R', 0) - count_char_from_index(s@, 'R', i as int),
            count_u == count_char_from_index(s@, 'U', 0) - count_char_from_index(s@, 'U', i as int),
            count_d == count_char_from_index(s@, 'D', 0) - count_char_from_index(s@, 'D', i as int)
    {
        if s[i] == 'L' {
            count_l += 1;
        } else if s[i] == 'R' {
            count_r += 1;
        } else if s[i] == 'U' {
            count_u += 1;
        } else if s[i] == 'D' {
            count_d += 1;
        }
        i += 1;
    }
    
    proof {
        count_char_equiv(s@, 'L');
        count_char_equiv(s@, 'R');
        count_char_equiv(s@, 'U');
        count_char_equiv(s@, 'D');
    }
    
    let lr_diff = if count_l >= count_r { count_l - count_r } else { count_r - count_l };
    let ud_diff = if count_u >= count_d { count_u - count_d } else { count_d - count_u };
    
    ((lr_diff + ud_diff) / 2) as i8
}
// </vc-code>


}

fn main() {}