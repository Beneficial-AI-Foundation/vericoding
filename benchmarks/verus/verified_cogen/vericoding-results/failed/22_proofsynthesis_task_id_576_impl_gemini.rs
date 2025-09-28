// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): added decreases clauses to both loops to prove termination. */
    let mut i: usize = 0;
    while i <= main.len() - sub.len()
        invariant
            0 <= i <= main.len() - sub.len() + 1,
            sub.len() <= main.len(),
            forall|k: int| 0 <= k < i as int ==> !(main@.subrange(k, k + sub.len() as int) =~= sub@),
        decreases main.len() - i, // or main.len() - sub.len() - i
    {
        let mut j: usize = 0;
        let mut is_match = true;
        while j < sub.len()
            invariant
                0 <= j <= sub.len(),
                i <= main.len() - sub.len(),
                is_match ==> (main@.subrange(i as int, (i + j) as int) =~= sub@.subrange(0, j as int)),
            decreases sub.len() - j,
        {
            if main[i + j] != sub[j] {
                is_match = false;
                break;
            }
            j = j + 1;
        }

        if is_match {
            assert(main@.subrange(i as int, (i + sub.len()) as int) =~= sub@);
            return true;
        }

        proof {
            assert(!is_match);
            assert(!(main@.subrange(i as int, (i + sub.len()) as int) =~= sub@));
        }

        i = i + 1;
    }

    return false;
}
// </vc-code>

}
fn main() {}