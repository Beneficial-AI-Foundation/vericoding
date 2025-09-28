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
/* helper modified by LLM (iteration 5): Added requires for char range to ensure safe casting; added #[verifier::truncate] on casts to fix overflow warnings */
fn three_char_to_int(s: &Vec<char>, start: usize) -> (r: i32)
    requires
        (start as int) + 3 <= s@.len(),
        forall|k: int| (start as int) <= k < (start as int) + 3 ==> s@[k] >= '0' && s@[k] <= '9',
    ensures
        r as int == 100 * ((s@[start as int] as int) - ('0' as int)) +
             10 * ((s@[start as int + 1] as int) - ('0' as int)) +
             ((s@[start as int + 2] as int) - ('0' as int)),
{
    let hundreds: i32 = #[verifier::truncate]((s[start] as i32) - ('0' as i32));
    let tens: i32 = #[verifier::truncate]((s[start + 1] as i32) - ('0' as i32));
    let units: i32 = #[verifier::truncate]((s[start + 2] as i32) - ('0' as i32));
    100 * hundreds + 10 * tens + units
}

/* helper modified by LLM (iteration 5): Added requires to ensure x is within safe range for abs to avoid overflow */
fn abs_diff_exec(x: i32) -> (r: i32)
    requires
        x >= -247 && x <= 642,
    ensures
        r as int == if x as int >= 0 { x as int } else { - (x as int) },
{
    if x >= 0 { x } else { -x }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires valid_input(s@)
    ensures is_minimum_difference(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added #[trigger] to quantifier for better verification */
    let n: usize = s.len() - 3;
    let mut min_diff: i32 = abs_diff_exec((753 as i32) - three_char_to_int(&s, 0));
    let mut i: usize = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            min_diff >= 0,
            forall |j: int| 0 <= j < i as int ==> min_diff as int <= abs_diff(753 - string_to_int(#[trigger] substring_at_index(s@, j))),
        decreases (n - i + 1) as int,
    {
        let current_diff: i32 = abs_diff_exec((753 as i32) - three_char_to_int(&s, i));
        if current_diff < min_diff {
            min_diff = current_diff;
        }
        i += 1;
    }
    min_diff
}
// </vc-code>


}

fn main() {}