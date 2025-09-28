// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn monotonic(l: Seq<int>) -> bool {
    if l.len() <= 1 {
        true
    } else {
        let increasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int];
        let decreasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int];
        increasing || decreasing
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_monotonic_invariant_sub(l: Seq<int>, i: int, j: int)
    requires
        monotonic(l),
        0 <= i <= j < l.len(),
    ensures
        if l[0] <= l[1] {
            l[i] <= l[j]
        } else {
            l[i] >= l[j]
        },
decreases j - i
{
    /* helper modified by LLM (iteration 5): Removed proof blocks from spec function */
    if l.len() <= 1 {
        return;
    }
    if l[0] <= l[1] {
        assert forall|k: nat| k < l.len() - 1 implies l[k as int] <= l[(k + 1) as int] by {
            assert(monotonic(l));
        };
        let mut k: int = i;
        while k < j
            invariant
                i <= k <= j,
                l[i] <= l[k],
            decreases j - k
        {
            assert(l[k] <= l[k + 1]);
            k = k + 1;
        }
    } else {
        assert forall|k: nat| k < l.len() - 1 implies l[k as int] >= l[(k + 1) as int] by {
            assert(monotonic(l));
        };
        let mut k: int = i;
        while k < j
            invariant
                i <= k <= j,
                l[i] >= l[k],
            decreases j - k
        {
            assert(l[k] >= l[k + 1]);
            k = k + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Vec<i8>) -> (result: bool)
    ensures result == monotonic(l@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed proof syntax */
    if l.len() <= 1 {
        return true;
    }
    let increasing = l[0] <= l[1];
    let mut i: usize = 0;
    while i < l.len() - 1
        invariant i <= l.len() - 1
    {
        let current = l[i];
        let next = l[i + 1];
        if increasing {
            if current > next {
                return false;
            }
        } else {
            if current < next {
                return false;
            }
        }
        i = i + 1;
    }
    true
}
// </vc-code>


}

fn main() {}