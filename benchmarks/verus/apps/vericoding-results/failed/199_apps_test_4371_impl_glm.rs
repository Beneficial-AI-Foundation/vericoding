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
/* helper modified by LLM (iteration 5): added preconditions and postconditions to ensure safe conversion */
fn chars_to_int(slice: &[char]) -> (num: i32)
    requires slice@.len() == 3
    requires forall|k: int| 0 <= k < 3 ==> '1' <= slice@[k] <= '9'
    ensures num as int == string_to_int(slice@)
    ensures 111 <= num <= 999
{
    let d1 = (#[verifier::truncate] slice[0] as i32) - ('0' as i32);
    let d2 = (#[verifier::truncate] slice[1] as i32) - ('0' as i32);
    let d3 = (#[verifier::truncate] slice[2] as i32) - ('0' as i32);
    100 * d1 + 10 * d2 + d3
}

/* helper modified by LLM (iteration 4): added absolute value function for i32 to avoid compilation error */
fn abs_i32(x: i32) -> (result: i32)
    ensures result as int == abs_diff(x as int)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires valid_input(s@)
    ensures is_minimum_difference(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant and added bounds for chars_to_int */
    let mut min_diff = 1000_i32;
    let mut i = 0;
    while i <= s.len() - 3
        invariant
            0 <= i <= s.len() - 2,
            min_diff >= 0,
            forall |j: int| 0 <= j < i ==> min_diff <= abs_diff(753 - string_to_int(substring_at_index(s@, j))),
            (i == 0 && min_diff == 1000) ||
            (i > 0 && exists |j: int| 0 <= j < i && min_diff == abs_diff(753 - string_to_int(substring_at_index(s@, j)))),
        decreases s.len() - 3 - i,
    {
        let arr = [s[i], s[i+1], s[i+2]];
        let num = chars_to_int(&arr);
        let diff = abs_i32(753_i32 - num);
        if diff < min_diff {
            min_diff = diff;
        }
        i = i + 1;
    }
    min_diff
}
// </vc-code>


}

fn main() {}