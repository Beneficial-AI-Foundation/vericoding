// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix int/nat mismatches for Seq indexing/skip and formalize step of count_true over skip */
proof fn lemma_count_true_skip_step(cond: Seq<bool>, i: int)
    requires
        0int <= i,
        i <= cond.len() as int,
    ensures
        if i < cond.len() as int {
            count_true(cond.skip(i)) == (if cond[i] { 1int } else { 0int }) + count_true(cond.skip(i + 1))
        } else {
            count_true(cond.skip(i)) == 0int
        },
{
    if i < cond.len() as int {
        let s = cond.skip(i);
        assert((s.len() as int) == cond.len() as int - i);
        assert(0int < s.len() as int);
        assert(s[0] == cond[i]);
        assert(s.skip(1) == cond.skip(i + 1));
        assert(count_true(s) == (if s[0] { 1int } else { 0int }) + count_true(s.skip(1)));
    } else {
        let s = cond.skip(i);
        assert(s.len() == 0);
        assert(count_true(s) == 0int);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int 
    decreases condition.len()
{
    if condition.len() == 0 {
        0int
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn extract(condition: Vec<bool>, arr: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == arr.len(),
        count_true(condition@) >= 0,
    ensures
        result.len() == count_true(condition@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): resolve int/nat mismatches in skip/indexing, maintain invariant via lemma, and build filtered result */
    let n = condition.len();
    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(condition@.skip(0int) == condition@);
    }
    while i < n
        invariant
            i <= n,
            condition.len() == n,
            arr.len() == n,
            0int <= i as int,
            res.len() as int + count_true(condition@.skip(i as int)) == count_true(condition@),
        decreases n as int - i as int
    {
        let b = condition[i];
        if b {
            let v = arr[i];
            res.push(v);
        }
        proof {
            lemma_count_true_skip_step(condition@, i as int);
        }
        i = i + 1;
    }
    proof {
        lemma_count_true_skip_step(condition@, n as int);
        assert(count_true(condition@.skip(n as int)) == 0int);
    }
    res
}
// </vc-code>

}
fn main() {}