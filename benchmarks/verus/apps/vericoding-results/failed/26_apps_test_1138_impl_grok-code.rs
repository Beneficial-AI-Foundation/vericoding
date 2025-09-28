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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures correct_result(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed integer literal syntax by removing invalid 'int' suffix and adding type annotations for runtime integers */
    if s.len() % 2 != 0 {
        -1i8
    } else {
        let mut num_L: i32 = 0;
        let mut num_R: i32 = 0;
        let mut num_U: i32 = 0;
        let mut num_D: i32 = 0;
        let mut i = 0usize;
        while i < s.len()
            invariant
                i <= s.len(),
                0 <= num_L <= i as i32,
                0 <= num_R <= i as i32,
                0 <= num_U <= i as i32,
                0 <= num_D <= i as i32,
                num_L == count_char(s@.subrange(0, i as int), 'L') as i32,
                num_R == count_char(s@.subrange(0, i as int), 'R') as i32,
                num_U == count_char(s@.subrange(0, i as int), 'U') as i32,
                num_D == count_char(s@.subrange(0, i as int), 'D') as i32,
            decreases (s.len() - i)
        {
            let cur = s[i];
            if cur == 'L' {
                num_L = num_L + 1;
            } else if cur == 'R' {
                num_R = num_R + 1;
            } else if cur == 'U' {
                num_U = num_U + 1;
            } else if cur == 'D' {
                num_D = num_D + 1;
            }
            i = i + 1;
        }
        let diff_lr = if num_L > num_R { num_L - num_R } else { num_R - num_L };
        let diff_ud = if num_U > num_D { num_U - num_D } else { num_D - num_U };
        let sum = diff_lr + diff_ud;
        let result_int = sum / 2;
        #[verifier::truncate]
        (result_int as i8)
    }
}
// </vc-code>


}

fn main() {}