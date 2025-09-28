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

proof fn count_char_helper_lemma(s: Seq<char>, c: char, index: int, count: int)
    requires 0 <= index <= s.len()
    ensures count_char_helper(s, c, index, count) == count + count_char_from_index(s, c, index)
    decreases s.len() - index
{
    if index >= s.len() {
    } else if s.index(index) == c {
        count_char_helper_lemma(s, c, index + 1, count + 1);
    } else {
        count_char_helper_lemma(s, c, index + 1, count);
    }
}

proof fn count_char_lemma(s: Seq<char>, c: char)
    ensures count_char(s, c) == count_char_from_index(s, c, 0)
{
    count_char_helper_lemma(s, c, 0, 0);
}

proof fn count_char_from_index_empty(s: Seq<char>, c: char, index: int)
    requires index >= s.len()
    ensures count_char_from_index(s, c, index) == 0
{
}

proof fn count_char_from_index_step(s: Seq<char>, c: char, index: int)
    requires index < s.len()
    ensures count_char_from_index(s, c, index) == (
        if s[index] == c {
            1 + count_char_from_index(s, c, index + 1)
        } else {
            count_char_from_index(s, c, index + 1)
        }
    )
{
}

/* helper modified by LLM (iteration 5): Fixed abs_i8 to prevent underflow in negative case */
fn abs_i8(x: i8) -> i8 {
    if x >= 0 { x } else { -x }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures correct_result(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed underflow issues and loop invariants */
    let n = s.len();
    if n % 2 != 0 {
        -1
    } else {
        let mut l_count: i8 = 0;
        let mut r_count: i8 = 0;
        let mut u_count: i8 = 0;
        let mut d_count: i8 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                i as nat <= n,
                l_count as int == count_char_from_index(s@, 'L', i),
                r_count as int == count_char_from_index(s@, 'R', i),
                u_count as int == count_char_from_index(s@, 'U', i),
                d_count as int == count_char_from_index(s@, 'D', i),
            decreases n - i
        {
            let c = s[i];
            match c {
                'L' => { l_count = l_count + 1; },
                'R' => { r_count = r_count + 1; },
                'U' => { u_count = u_count + 1; },
                'D' => { d_count = d_count + 1; },
                _ => {},
            }
            proof {
                count_char_from_index_step(s@, 'L', i);
                count_char_from_index_step(s@, 'R', i);
                count_char_from_index_step(s@, 'U', i);
                count_char_from_index_step(s@, 'D', i);
            }
            i += 1;
        }
        proof {
            count_char_from_index_empty(s@, 'L', n);
            count_char_from_index_empty(s@, 'R', n);
            count_char_from_index_empty(s@, 'U', n);
            count_char_from_index_empty(s@, 'D', n);
        }
        let diff_lr = abs_i8(l_count - r_count);
        let diff_ud = abs_i8(u_count - d_count);
        (diff_lr + diff_ud) / 2
    }
}
// </vc-code>


}

fn main() {}