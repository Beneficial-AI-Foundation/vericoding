// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): seq_eq_at expresses that sub equals main subrange starting at k */
spec fn seq_eq_at(main: &Vec<i32>, sub: &Vec<i32>, k: int) -> bool {
    0 <= k && k <= (main.len() as int) - (sub.len() as int) && main@.subrange(k, k + (sub.len() as int)) =~= sub@
}
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
    /* code modified by LLM (iteration 5): iterate with int indices and maintain invariants to ensure safe indexing and prove subrange equality when found */
    let max_k: int = (main.len() as int) - (sub.len() as int);
    let mut k: int = 0;
    let mut res: bool = false;
    while k <= max_k
        invariant
            0 <= k <= max_k + 1,
        decreases max_k + 1 - k
    {
        if !res {
            let sub_len: int = sub.len() as int;
            let main_len: int = main.len() as int;
            let mut j: int = 0;
            let mut all_eq: bool = true;
            while j < sub_len
                invariant
                    0 <= j <= sub_len,
                    forall|i: int| 0 <= i && i < j ==> main@@[k + i] == sub@@[i],
                    k + j < main_len,
                decreases sub_len - j
            {
                if main[(k + j) as usize] != sub[j as usize] {
                    all_eq = false;
                    j = sub_len;
                } else {
                    j = j + 1;
                }
            }
            if all_eq {
                proof {
                    assert(forall|i: int| 0 <= i && i < sub_len ==> main@@[k + i] == sub@@[i]);
                    assert(main@.subrange(k, k + sub_len) =~= sub@);
                }
                res = true;
            }
        }
        k = k + 1;
    }
    res
}
// </vc-code>

}
fn main() {}