// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial no-op lemma to satisfy placeholder */
proof fn lemma_noop_arange() {
    // no-op helper
}

// </vc-helpers>

// <vc-spec>
spec fn arange_length(start: int, stop: int, step: int) -> nat
{
    if step != 0 {
        if step < 0 {
            if start > stop {
                ((start - stop) / (-step)) as nat
            } else {
                0
            }
        } else {
            if start < stop {
                ((stop - start) / step) as nat
            } else {
                0
            }
        }
    } else {
        0
    }
}

fn arange(start: i8, stop: i8, step: i8) -> (result: Vec<i8>)
    requires 
        step != 0,
        if step < 0 { start > stop } else { start < stop },
    ensures
        result@.len() == arange_length(start as int, stop as int, step as int),
        result@.len() > 0,
        result@[0] == start as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute tracked length and populate Vec using tracked nat counters */
    let tracked n: nat = arange_length(start as int, stop as int, step as int);
    let mut result_vec: Vec<i8> = Vec::new();
    let tracked mut i: nat = 0;
    let mut cur: i8 = start;
    while i < n
        invariant
            i <= n,
            result_vec@.len() == i,
        decreases n - i
    {
        result_vec.push(cur);
        cur = (cur as i32 + step as i32) as i8;
        i = i + 1;
    }
    proof {
        assert(i == n);
        assert(result_vec@.len() == n);
    }
    result_vec
}

// </vc-code>


}
fn main() {}