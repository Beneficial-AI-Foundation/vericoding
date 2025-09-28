// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use integer indexing with .index method to fix compilation error */
fn sub_array_equals(main: &Vec<i32>, start: usize, sub: &Vec<i32>) -> bool
    requires
        start + sub.len() <= main.len(),
{
    let m = sub.len();
    let start_int = start as int;
    let m_int = m as int;
    for j in 0..m_int
        invariant
            0 <= j <= m_int,
            forall|k: int| 0 <= k < j ==> main@[start_int + k] == sub@[k],
    {
        if main@.index(start_int + j) != sub@.index(j) {
            return false;
        }
    }
    true
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
/* code modified by LLM (iteration 5): fixed indices to int type in subrange and invariant */
{
    let n = main.len();
    let m = sub.len();
    if m > n {
        return false;
    }
    for i in 0..(n - m + 1)
        invariant
            forall|k: int| 0 <= k < (i as int) ==> !(main@.subrange(k, (k + m) as int) =~= sub@),
    {
        if sub_array_equals(main, i, sub) {
            proof {
                assert(main@.subrange(i as int, (i + m) as int) =~= sub@);
            }
            return true;
        }
    }
    false
}
// </vc-code>

}
fn main() {}