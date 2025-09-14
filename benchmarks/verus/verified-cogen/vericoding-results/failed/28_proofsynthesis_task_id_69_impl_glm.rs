// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 4): fixed compilation error by replacing sub.is_empty() with sub.len() == 0 */
{
    if sub.len() == 0 {
        return true;
    }

    let len_main = main.len();
    let len_sub = sub.len();
    for i in 0..(len_main - len_sub + 1) {
        let mut all_match = true;
        for j in 0..len_sub {
            if main[i + j] != sub[j] {
                all_match = false;
                break;
            }
        }
        if all_match {
            return true;
        }
    }
    return false;
}
// </vc-code>

}
fn main() {}