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
fn compute_abs_diff(x: i32) -> (r: i32)
    ensures r as int == abs_diff(x as int),
{
    if x >= 0 { x } else { -x }
}

fn compute_string_to_int(s_slice: &[char]) -> (r: i32)
    requires
        s_slice.len() == 3,
        forall|i: int| 0 <= i < 3 ==> s_slice@.index(i) >= '1' && s_slice@.index(i) <= '9',
    ensures
        r as int == string_to_int(s_slice@),
{
    let d1 = s_slice[0] as i32 - '0' as i32;
    let d2 = s_slice[1] as i32 - '0' as i32;
    let d3 = s_slice[2] as i32 - '0' as i32;
    100 * d1 + 10 * d2 + d3
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires valid_input(s@)
    ensures is_minimum_difference(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Used `subslice` to fix compilation error for slicing.] */
    let s_slice = s.as_slice();

    let first_sub = subslice(s_slice, 0, 3);
    let first_num = compute_string_to_int(first_sub);
    let mut min_diff = compute_abs_diff(753 - first_num);

    let mut i: usize = 1;
    while i <= s.len() - 3
        invariant
            1 <= i <= s.len() - 2,
            valid_input(s@),
            min_diff >= 0,
            exists|j: int| 0 <= j < i &&
                min_diff == abs_diff(753 - string_to_int(#[trigger] substring_at_index(s@, j))),
            forall|j: int| 0 <= j < i ==> 
                min_diff <= abs_diff(753 - string_to_int(#[trigger] substring_at_index(s@, j))),
        decreases (s.len() - 3) - i
    {
        let current_sub = subslice(s_slice, i, i + 3);
        let current_num = compute_string_to_int(current_sub);
        let current_diff = compute_abs_diff(753 - current_num);

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