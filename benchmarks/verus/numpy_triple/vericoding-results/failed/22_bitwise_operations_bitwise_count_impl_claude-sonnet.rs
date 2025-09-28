// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(x: i32) -> nat {
    if x >= 0 { x as nat } else { (-x) as nat }
}

spec fn popcount(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 2) + popcount(n / 2)
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_popcount_of_abs_nonneg(x: i32)
    requires x >= 0
    ensures popcount(abs_spec(x)) == popcount(x as nat)
{
}

proof fn lemma_popcount_of_abs_neg(x: i32)
    requires x < 0
    ensures popcount(abs_spec(x)) == popcount((-x) as nat)
{
}

proof fn lemma_popcount_zero()
    ensures popcount(0) == 0
{
}

fn compute_popcount(n: nat) -> (result: nat)
    ensures result == popcount(n)
    decreases n
{
    if n == 0 {
        0
    } else {
        let bit = n % 2;
        let rest = compute_popcount(n / 2);
        bit + rest
    }
}

/* helper modified by LLM (iteration 5): return u32 instead of nat to avoid casting errors */
fn abs_nat(x: i32) -> (result: u32)
    ensures result as nat == abs_spec(x)
{
    if x >= 0 {
        x as u32
    } else {
        (-x) as u32
    }
}
// </vc-helpers>

// <vc-spec>
fn bitwise_count(x: Vec<i32>) -> (result: Vec<nat>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == popcount(abs_spec(x[i])),
        forall|i: int| 0 <= i < result.len() ==> x[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost variable for abs_val as nat */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == popcount(abs_spec(x[j])),
    {
        let abs_val_u32 = abs_nat(x[i]);
        let ghost abs_val_nat = abs_val_u32 as nat;
        let count = compute_popcount(abs_val_nat);
        result.push(count);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}