// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section remains empty as no specific helper functions are required for this problem. */
// </vc-helpers>

// <vc-spec>
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

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
/* code modified by LLM (iteration 5): Fixed compilation error by ensuring correct type casting for `sub.len()` and parenthesization in loop invariants and assertions. Added an assertion to ensure the loop invariant reflects the properties of sub-array matching. */
{
    if sub.len() == 0 {
        return true;
    }

    if main.len() < sub.len() {
        return false;
    }

    let mut i: int = 0;
    while i <= (main.len() as int - sub.len() as int)
        invariant
            0 <= i,
            i <= (main.len() as int - sub.len() as int) + 1,
            // Loop invariant (i) correctly shows that if a match was found for any `k` up to `i-1` it would have returned true
            forall|k: int| 0 <= k < i ==> !(#[trigger] (main@.subrange(k, k + sub.len() as int))) =~= sub@,
    {
        let mut j: int = 0;
        while j < sub.len() as int
            invariant
                0 <= i,
                i <= (main.len() as int - sub.len() as int),
                0 <= j <= sub.len() as int,
                forall|k: int| 0 <= k < j ==> main@[i + k] == sub@[k],
        {
            if main@[i + j] != sub@[j] {
                break;
            }
            j = j + 1;
        }

        if j == sub.len() as int {
            assert(
                exists|k: int, l: int|
                    (0 <= k && k <= (main.len() as int - sub.len() as int) && l == k + sub.len() as int
                        && (#[trigger] (main@.subrange(k, l))) =~= sub@),
            ) by {
                // The existence of k and l is proven by setting k = i and l = i + sub.len()
                assert(i + sub.len() as int == i + sub.len() as int);
                assert(main@.subrange(i, (i + sub.len() as int)) =~= sub@);
            };
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}