// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<i32>, i: int) -> int
    recommends 
        0 <= i < a.len(),
    decreases i
{
    if 0 <= i < a.len() {
        a[i] as int + if i == 0 { 0 } else { sum(a, i - 1) }
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [add lemma for sum(0)] */
proof fn sum_induction_lemma(a: Seq<i32>, i: int)
    requires
        0 < i < a.len(),
    ensures
        sum(a, i) == sum(a, i - 1) + (a[i] as int),
{
}

proof fn sum_of_zero_is_first_element(a: Seq<i32>)
    requires
        a.len() > 0,
    ensures
        sum(a, 0) == a[0] as int,
{
}
// </vc-helpers>

// <vc-spec>
fn cumsum(a: &[i32], b: &mut [i32])
    requires 
        a.len() == old(b).len(),
        a.len() > 0,
    ensures 
        forall|i: int| 0 <= i < a.len() ==> b[i] as int == sum(a@, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [separate first iteration to simplify invariants] */
    b[0] = a[0];

    let mut i: usize = 1;
    while i < a.len()
        invariant
            a.len() == old(b).len(),
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> b@[j] as int == sum(a@, j),
        decreases a.len() - i
    {
        proof {
            sum_induction_lemma(a@, i as int);
            let prev_idx = (i - 1) as int;
            assert(b@[prev_idx] as int == sum(a@, prev_idx));
        }

        let prev = b[i - 1];
        let current = a[i];

        b[i] = prev + current;

        proof {
            let current_idx = i as int;
            let prev_idx = (i - 1) as int;
            assert(b@[current_idx] as int == (prev as int) + (current as int));
            assert(b@[current_idx] as int == sum(a@, prev_idx) + a@[current_idx] as int);
            assert(b@[current_idx] as int == sum(a@, current_idx));
            assert(forall|j: int| 0 <= j < i ==> b@[j] as int == sum(a@, j));
            assert(forall|j: int| 0 <= j <= i ==> b@[j] as int == sum(a@, j));
        }

        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}