// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No additional helpers needed beyond the standard simple implementations */
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
    /* code modified by LLM (iteration 5): Fixed compilation error by correcting syntax of decreases clauses (removed unnecessary parentheses) */
    let m_len = main.len();
    let s_len = sub.len();
    let mut k: usize = 0;
    while k <= m_len - s_len
        decreases m_len as int - s_len as int - k as int
        invariant
            k as int <= (m_len - s_len) as int + 1,
            forall |a: int, b: int| 0 <= a <= (m_len - s_len) as int && b == a + s_len as int ==> (main@.subrange(a, b) =~= sub@) == false || a >= k as int
    {
        let mut match_found = true;
        let mut i: usize = 0;
        while i < s_len
            decreases s_len as int - i as int
            invariant
                i as int <= s_len as int,
                match_found == (forall |j: int| 0 <= j < i as int ==> main@[k as int + j] == sub@[j])
        {
            if main[k + i] != sub[i] {
                match_found = false;
                break;
            }
            i = i + 1;
        }
        if match_found {
            assert(main@.subrange(k as int, (k + s_len) as int) =~= sub@);
            return true;
        }
        k = k + 1;
    }
    false
}
// </vc-code>

}
fn main() {}