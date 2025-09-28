// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): seq_prefix over Seq with int n, requires 0 <= n <= len */
spec fn seq_prefix(ops: Seq<i32>, n: int) -> i32
    requires 0 <= n && n <= ops.len()
    decreases n
{
    if n == 0 { 0 } else { let m = n - 1; seq_prefix(ops, m) + ops[m] }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute prefix sums using Vec and Vec.view() for spec-level invariants */
    let mut prefix: Vec<i32> = Vec::new();
    prefix.push(0);
    let mut any_neg: bool = false;
    let n: usize = operations.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            prefix.len() == i + 1,
            forall|j: int| 0 <= j < i as int ==> prefix.view()[j + 1] == prefix.view()[j] + operations.view()[j],
        decreases n - i
    {
        let op: i32 = operations[i];
        let next: i32 = prefix[i] + op;
        prefix.push(next);
        if next < 0 {
            any_neg = true;
        }
        i += 1;
    }
    (prefix, any_neg)
}
// </vc-code>

}
fn main() {}