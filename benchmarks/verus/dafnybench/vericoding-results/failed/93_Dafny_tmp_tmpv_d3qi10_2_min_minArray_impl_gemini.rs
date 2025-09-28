// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

spec fn min_function(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause and changed recommends to requires */
spec fn min_seq(s: Seq<i32>) -> int
    requires s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0] as int
    } else {
        min(s.last() as int, min_seq(s.drop_last()))
    }
}

proof fn min_le_forall(s: Seq<i32>)
    requires s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> min_seq(s) <= s[i]
    decreases s.len()
{
    if s.len() > 1 {
        min_le_forall(s.drop_last());
    }
}

proof fn min_in_seq_idx(s: Seq<i32>) -> (idx: int)
    requires s.len() > 0
    ensures 
        0 <= idx < s.len(),
        min_seq(s) == s[idx],
    decreases s.len()
{
    if s.len() == 1 {
        0
    } else {
        let prefix = s.drop_last();
        let prefix_idx = min_in_seq_idx(prefix);
        let m_prefix = min_seq(prefix);
        if s.last() < m_prefix {
            (s.len() - 1) as int
        } else {
            prefix_idx
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures 
        forall|k: int| 0 <= k < a.len() ==> m <= a[k],
        exists|k: int| 0 <= k < a.len() && m == a[k]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): no change, logic from previous iteration is sound */
    let mut m = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            m as int == min_seq(a.view().subrange(0, i as int)),
        decreases a.len() - i
    {
        if a[i] < m {
            m = a[i];
        }
        i = i + 1;
    }

    proof {
        min_le_forall(a.view());
        min_in_seq_idx(a.view());
    }

    m
}
// </vc-code>

}
fn main() {}