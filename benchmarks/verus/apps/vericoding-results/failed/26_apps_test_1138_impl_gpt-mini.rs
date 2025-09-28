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
/* helper modified by LLM (iteration 4): abs difference bounded by sum */
proof fn abs_le_sum(a: int, b: int)
    requires
        a >= 0,
        b >= 0,
    ensures
        abs(a - b) <= a + b,
{
    if a >= b {
        assert(abs(a - b) == a - b);
        assert(a - b <= a + b);
    } else {
        assert(abs(a - b) == b - a);
        assert(b - a <= a + b);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures correct_result(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute primitive absolute values without using .abs on Verus int and prove relation to spec abs */
    let n = s.len();
    if n % 2 != 0 {
        return -1;
    }

    let mut i: usize = 0;
    let mut l: i32 = 0;
    let mut r: i32 = 0;
    let mut u_: i32 = 0;
    let mut d: i32 = 0;

    while i < n
        invariant
            0 <= i,
            i <= n,
            (l as int) == count_char(s@, 'L') - count_char_from_index(s@, 'L', i as int),
            (r as int) == count_char(s@, 'R') - count_char_from_index(s@, 'R', i as int),
            (u_ as int) == count_char(s@, 'U') - count_char_from_index(s@, 'U', i as int),
            (d as int) == count_char(s@, 'D') - count_char_from_index(s@, 'D', i as int),
        decreases
            n - i
    {
        let c = s[i];
        if c == 'L' {
            l = l + 1;
        } else if c == 'R' {
            r = r + 1;
        } else if c == 'U' {
            u_ = u_ + 1;
        } else {
            d = d + 1;
        }
        i = i + 1;
    }

    let lr_abs_i32: i32 = if l >= r { l - r } else { r - l };
    let ud_abs_i32: i32 = if u_ >= d { u_ - d } else { d - u_ };
    let result_prim_i32: i32 = (lr_abs_i32 + ud_abs_i32) / 2;

    proof {
        assert((l as int) == count_char(s@, 'L'));
        assert((r as int) == count_char(s@, 'R'));
        assert((u_ as int) == count_char(s@, 'U'));
        assert((d as int) == count_char(s@, 'D'));

        if l >= r {
            assert((lr_abs_i32 as int) == (l - r) as int);
            assert((l - r) as int == l as int - r as int);
            assert(abs(l as int - r as int) == l as int - r as int);
        } else {
            assert((lr_abs_i32 as int) == (r - l) as int);
            assert((r - l) as int == r as int - l as int);
            assert(abs(l as int - r as int) == -(l as int - r as int));
        }

        if u_ >= d {
            assert((ud_abs_i32 as int) == (u_ - d) as int);
            assert((u_ - d) as int == u_ as int - d as int);
            assert(abs(u_ as int - d as int) == u_ as int - d as int);
        } else {
            assert((ud_abs_i32 as int) == (d - u_) as int);
            assert((d - u_) as int == d as int - u_ as int);
            assert(abs(u_ as int - d as int) == -(u_ as int - d as int));
        }

        assert((result_prim_i32 as int) == (abs(l as int - r as int) + abs(u_ as int - d as int)) / 2);
        assert(result_prim_i32 >= 0);

        abs_le_sum(count_char(s@, 'L'), count_char(s@, 'R'));
        abs_le_sum(count_char(s@, 'U'), count_char(s@, 'D'));
        assert(abs(count_char(s@, 'L') - count_char(s@, 'R')) + abs(count_char(s@, 'U') - count_char(s@, 'D')) <=
               count_char(s@, 'L') + count_char(s@, 'R') + count_char(s@, 'U') + count_char(s@, 'D'));
        assert(count_char(s@, 'L') + count_char(s@, 'R') + count_char(s@, 'U') + count_char(s@, 'D') == s.len() as int);
        assert((result_prim_i32 as int) <= s.len() as int / 2);
    }

    result_prim_i32 as i8
}

// </vc-code>


}

fn main() {}