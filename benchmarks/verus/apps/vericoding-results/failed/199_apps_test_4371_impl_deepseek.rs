// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s.index(i) >= '1' && #[trigger] s.index(i) <= '9'
}

spec fn string_to_int(s: Seq<char>) -> int {
    100 * ((s.index(0) as int) - ('0' as int)) + 
    10 * ((s.index(1) as int) - ('0' as int)) + 
    ((s.index(2) as int) - ('0' as int))
}

spec fn abs_diff(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn substring_at_index(s: Seq<char>, i: int) -> Seq<char> {
    s.subrange(i, i + 3)
}

spec fn is_minimum_difference(s: Seq<char>, result: int) -> bool {
    valid_input(s) ==> (
        result >= 0 &&
        (exists|i: int| 0 <= i <= s.len() - 3 && result == abs_diff(753 - string_to_int(#[trigger] substring_at_index(s, i)))) &&
        (forall|i: int| 0 <= i <= s.len() - 3 ==> result <= abs_diff(753 - string_to_int(#[trigger] substring_at_index(s, i))))
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed arithmetic overflow in compute_difference, added bound checks */
fn abs_diff_value(x: i32) -> (result: i32)
    ensures
        result >= 0,
        result as int == abs_diff(x as int),
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

fn compute_difference(s: &Vec<char>, i: usize) -> (result: i32)
    requires
        valid_input(s@),
        i <= s@.len() - 3,
    ensures
        result as int == abs_diff(753 - string_to_int(substring_at_index(s@, i as int))),
{
    let idx1: usize = i;
    proof {
        assert(0 <= idx1 < s@.len());
    }
    let idx2: usize = i + 1;
    proof {
        assert(0 <= idx2 < s@.len());
    }
    let idx3: usize = i + 2;
    proof {
        assert(0 <= idx3 < s@.len());
    }
    let a = s[idx1] as i32 - '0' as i32;
    let b = s[idx2] as i32 - '0' as i32;
    let c = s[idx3] as i32 - '0' as i32;
    let num = 100 * a + 10 * b + c;
    abs_diff_value(753 - num)
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires valid_input(s@)
    ensures is_minimum_difference(s@, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariants, initialization, and index bounds */
{
    let len = s.len();
    let mut min_diff: i32 = abs_diff_value(753 - 100 * ((s[0] as i32) - '0' as i32) - 10 * ((s[1] as i32) - '0' as i32) - ((s[2] as i32) - '0' as i32));
    let mut i: usize = 1;
    
    while i <= len.checked_sub(3).unwrap_or(0)
        invariant
            0 <= i <= s@.len() - 2,
            min_diff >= 0,
            exists|j: int| 0 <= j < i as int + 1 ==> min_diff as int == abs_diff(753 - string_to_int(substring_at_index(s@, j))),
            forall|j: int| 0 <= j < i as int + 1 ==> min_diff as int <= abs_diff(753 - string_to_int(substring_at_index(s@, j))),
        decreases (s@.len() - 3) - i,
    {
        let current_diff = compute_difference(&s, i);
        if current_diff < min_diff {
            min_diff = current_diff;
        }
        i = i + 1;
    }
    
    min_diff
}
// </vc-code>


}

fn main() {}