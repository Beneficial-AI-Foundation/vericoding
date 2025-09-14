// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added int casts in indexing to match expected types */
spec fn seq_matches(main: Seq<i32>, sub: Seq<i32>, start: int) -> bool
    recommends
        0 <= start <= main.len() - sub.len(),
        sub.len() >= 0,
    {
        forall|i: nat| 0 <= i < sub.len() ==> #[trigger] main[start + (i as int)] == sub[(i as int)]
}
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
/* code modified by LLM (iteration 5): Replace @@ with @ and add int casts for indexing */
{
    let main_len: usize = main.len();
    let sub_len: usize = sub.len();
    
    if sub_len == 0 {
        return true;
    }
    
    let mut k: usize = 0;
    while k <= main_len - sub_len
        invariant
            0 <= k <= main_len - sub_len + 1,
            forall |start: nat| 0 <= start < k ==> !seq_matches(main@, sub@, start as int),
    {
        let mut i: usize = 0;
        let mut matched = true;
        while i < sub_len
            invariant
                0 <= i <= sub_len,
                matched == forall |j: usize| 0 <= j < i ==> main@[(k + j) as int] == sub@[j],
        {
            if main[k + i] != sub[i] {
                matched = false;
                // note: no break in Verus, continue to set i to sub_len
                i = sub_len;
            } else {
                i = i + 1;
            }
        }
        if matched {
            // found a match
            return true;
        }
        k = k + 1;
    }
    // no match found
    false
}
// </vc-code>

}
fn main() {}