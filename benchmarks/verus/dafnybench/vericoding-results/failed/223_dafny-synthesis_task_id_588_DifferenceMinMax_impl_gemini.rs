// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.take(a.len() - 1);
        let min_prefix = min(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max(a: Seq<int>) -> int
    recommends a.len() > 0  
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.take(a.len() - 1);
        let max_prefix = max(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): made helper functions public */
pub proof fn min_unfold(s: Seq<int>)
    requires
        s.len() > 1,
    ensures
        min(s) == if s[s.len() - 1] <= min(s.take(s.len() - 1)) { s[s.len() - 1] } else { min(s.take(s.len() - 1)) },
{
}

pub proof fn max_unfold(s: Seq<int>)
    requires
        s.len() > 1,
    ensures
        max(s) == if s[s.len() - 1] >= max(s.take(s.len() - 1)) { s[s.len() - 1] } else { max(s.take(s.len() - 1)) },
{
}
// </vc-helpers>

// <vc-spec>
fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires a.len() > 0
    ensures diff == max(a@.map(|i, x| x as int)) - min(a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed comparison operators to exactly match spec and resolve invariant errors */
    let mut min_val = a[0];
    let mut max_val = a[0];
    let mut i: usize = 1;

    while i < a.len()
        invariant
            a.len() > 0,
            1 <= i <= a.len(),
            min_val as int == min(a@.map(|_idx, val| val as int).take(i as int)),
            max_val as int == max(a@.map(|_idx, val| val as int).take(i as int)),
        decreases a.len() - i
    {
        let current_val = a[i];

        proof {
            let s = a@.map(|_idx, val| val as int);
            let s_next = s.take((i + 1) as int);
            min_unfold(s_next);
            max_unfold(s_next);
        }

        if current_val <= min_val {
            min_val = current_val;
        }
        if current_val >= max_val {
            max_val = current_val;
        }
        i = i + 1;
    }

    max_val - min_val
}
// </vc-code>

}
fn main() {}