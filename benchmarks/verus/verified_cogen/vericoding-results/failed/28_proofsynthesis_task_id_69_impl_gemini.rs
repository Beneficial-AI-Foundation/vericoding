// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    requires
        sub.len() <= main.len(),

    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using slice range syntax */
    let main_len = main.len();
    let sub_len = sub.len();

    if sub_len == 0 {
        return true;
    }

    let mut k: usize = 0;
    while k <= main_len - sub_len
        invariant
            main.len() == main_len,
            sub.len() == sub_len,
            sub_len <= main.len(),
            0 <= k && k <= main_len - sub_len + 1,
            forall|i: int| 0 <= i < (k as int) ==> !(main@.subrange(i, i + sub_len as int) =~= sub@),
        decreases main_len - k
    {
        if &main[k..(k + sub_len)] == sub.as_slice() {
            return true;
        }
        k = k + 1;
    }

    false
}
// </vc-code>

}
fn main() {}