// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Split the main loop invariant into two forall expressions for clarity, which is logically equivalent but can sometimes help the prover. */
    let mut c: Vec<i32> = Vec::new();
    c.resize(a.len(), 0i32);
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            c.len() == a.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < i as int ==> (
                (i32::MIN <= (a@[j] as int) + (b@[j] as int) <= i32::MAX) &&
                c@[j] == a@[j] + b@[j]
            ),
            forall|j: int| i as int <= j < a.len() as int ==> c@[j] == 0,
        decreases a.len() - i
    {
        assert(i32::MIN <= (a@[i as int] as int) + (b@[i as int] as int) <= i32::MAX);
        let sum = a[i] + b[i];
        c.set(i, sum);
        i = i + 1;
    }
    c
}
// </vc-code>

}
fn main() {}