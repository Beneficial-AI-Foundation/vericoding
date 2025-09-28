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
/* helper modified by LLM (iteration 5): Added missing lemma to prove count_char equals count_char_from_index */
proof fn count_char_is_count_from_zero(s: Seq<char>, c: char)
    ensures count_char(s, c) == count_char_from_index(s, c, 0)
    decreases s.len()
{
    if s.len() == 0 {
        assert(count_char(s, c) == count_char_helper(s, c, 0, 0));
        assert(count_char_from_index(s, c, 0) == 0);
    } else {
        count_char_helper_equals_count_from_index(s, c, 0, 0);
    }
}

proof fn count_char_helper_equals_count_from_index(s: Seq<char>, c: char, index: int, count: int)
    requires 0 <= index <= s.len()
    ensures count_char_helper(s, c, index, count) == count + count_char_from_index(s, c, index)
    decreases s.len() - index
{
    if index >= s.len() {
        assert(count_char_helper(s, c, index, count) == count);
        assert(count_char_from_index(s, c, index) == 0);
    } else if s[index] == c {
        count_char_helper_equals_count_from_index(s, c, index + 1, count + 1);
    } else {
        count_char_helper_equals_count_from_index(s, c, index + 1, count);
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
    /* code modified by LLM (iteration 5): Fixed type issues and use seq slice instead of subrange */
    let n = s.len();
    
    if n % 2 != 0 {
        return -1;
    }
    
    let mut count_l: int = 0int;
    let mut count_r: int = 0int;
    let mut count_u: int = 0int;
    let mut count_d: int = 0int;
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            i <= s.len(),
            count_l >= 0,
            count_r >= 0,
            count_u >= 0,
            count_d >= 0,
            count_l == count_char_from_index(s@.subrange(0int, i as int), 'L', 0),
            count_r == count_char_from_index(s@.subrange(0int, i as int), 'R', 0),
            count_u == count_char_from_index(s@.subrange(0int, i as int), 'U', 0),
            count_d == count_char_from_index(s@.subrange(0int, i as int), 'D', 0),
            valid_input(s@),
        decreases n - i
    {
        let ch = s[i];
        if ch == 'L' {
            count_l = count_l + 1int;
        } else if ch == 'R' {
            count_r = count_r + 1int;
        } else if ch == 'U' {
            count_u = count_u + 1int;
        } else if ch == 'D' {
            count_d = count_d + 1int;
        }
        i = i + 1;
    }
    
    proof {
        count_char_is_count_from_zero(s@, 'L');
        count_char_is_count_from_zero(s@, 'R');
        count_char_is_count_from_zero(s@, 'U');
        count_char_is_count_from_zero(s@, 'D');
        assert(s@.subrange(0int, n as int) =~= s@);
        assert(count_l == count_char(s@, 'L'));
        assert(count_r == count_char(s@, 'R'));
        assert(count_u == count_char(s@, 'U'));
        assert(count_d == count_char(s@, 'D'));
    }
    
    let diff_lr: int = if count_l >= count_r { count_l - count_r } else { count_r - count_l };
    let diff_ud: int = if count_u >= count_d { count_u - count_d } else { count_d - count_u };
    
    assert(diff_lr == abs(count_l - count_r));
    assert(diff_ud == abs(count_u - count_d));
    assert(diff_lr >= 0);
    assert(diff_ud >= 0);
    assert(diff_lr + diff_ud >= 0);
    assert((diff_lr + diff_ud) / 2int >= 0);
    assert((diff_lr + diff_ud) / 2int <= n as int / 2int);
    
    let result_int: int = (diff_lr + diff_ud) / 2int;
    assert(result_int >= 0);
    assert(result_int <= 127);
    let result = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}