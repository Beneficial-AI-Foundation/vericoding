// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count(hi: nat, s: Seq<i32>) -> int
    decreases hi
{
    if hi == 0 {
        0
    } else if s[hi - 1] % 2 == 0 {
        1 + count((hi - 1) as nat, s)
    } else {
        count((hi - 1) as nat, s)
    }
}

fn compute_count(count_index: usize, a: &Vec<i32>, b: &mut Vec<i32>) -> (p: usize)
    requires 
        count_index == 0 || (a.len() == old(b).len() && 1 <= count_index <= a.len()),
    ensures 
        p == count(count_index as nat, a@),
{
  assume(false);
  0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [retained helper for proving non-negativity] */
proof fn count_non_negative(hi: nat, s: Seq<i32>)
    requires hi <= s.len(),
    ensures count(hi, s) >= 0,
    decreases hi
{
    if hi > 0 {
        count_non_negative((hi - 1) as nat, s);
    }
}

/* helper modified by LLM (iteration 5): [added lemma to prove count is bounded by hi] */
proof fn count_le_hi(hi: nat, s: Seq<i32>)
    requires hi <= s.len(),
    ensures count(hi, s) <= hi as int,
    decreases hi
{
    if hi > 0 {
        count_le_hi((hi - 1) as nat, s);
        assert(count(hi, s) == if s[hi - 1] % 2int == 0 { 1 + count(hi-1, s) } else { count(hi-1, s) });
    }
}
// </vc-helpers>

// <vc-spec>
fn pre_compute(a: &Vec<i32>, b: &mut Vec<i32>) -> (p: usize)
    requires 
        a.len() == old(b).len(),
    ensures 
        (b.len() == 0 || (a.len() == b.len() && 1 <= b.len() <= a.len())) &&
        p == count(b.len() as nat, a@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [fixed compilation error and added supporting proofs] */
{
    let mut i: usize = 0;
    let mut p: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            p <= i,
            p as int == count(i as nat, a@),
            a.len() == old(b).len(),
            b.len() == old(b).len(),
        decreases a.len() - i
    {
        proof {
            count_non_negative(i as nat, a@);
            count_le_hi(i as nat, a@);
        }

        assert(count((i + 1) as nat, a@) ==
            if a@[i as nat] % 2int == 0 {
                1 + count(i as nat, a@)
            } else {
                count(i as nat, a@)
            }
        ) by {};

        if a[i] % 2 == 0 {
            p = p + 1;
        }
        i = i + 1;
    }
    proof {
        count_non_negative(a.len() as nat, a@);
    }
    p
}
// </vc-code>

}
fn main() {}