// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): placeholder - no changes needed */
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
/* code modified by LLM (iteration 5): Fixed compilation error by removing incorrect comma in invariant. */
{
    if sub.len() == 0 {
        return true;
    }
    if main.len() == 0 {
        return false;
    }

    let main_len = main.len();
    let sub_len = sub.len();

    if sub_len > main_len {
        return false;
    }

    let mut i: usize = 0;
    while i <= (main_len - sub_len)
        invariant
            0 <= i as int,
            i as int <= (main_len - sub_len) as int + 1,
            main_len >= sub_len ==> (i <= (main_len - sub_len) + 1),
            forall|k: int|
                0 <= k < i as int && k <= (main_len - sub_len) as int
                    ==> !((main@.subrange(k, (k + sub_len) as int)) =~= sub@),
    {
        let mut j: usize = 0;
        while j < sub_len
            invariant
                0 <= i as int,
                0 <= j as int,
                j as int <= sub_len as int,
                i <= (main_len - sub_len),
                main_len > 0,
                sub_len > 0,
                forall|k: int|
                    0 <= k < i as int && k <= (main_len - sub_len) as int
                        ==> !((main@.subrange(k, (k + sub_len) as int)) =~= sub@),
                (i as int + j as int) < main_len as int,
                j as int < sub_len as int,
                forall|idx: int|
                    0 <= idx < j as int
                        ==> main[i + idx] != sub[idx]
        {
            if main[i + j] != sub[j] {
                break;
            }
            j = j + 1;
        }

        if j == sub_len {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}