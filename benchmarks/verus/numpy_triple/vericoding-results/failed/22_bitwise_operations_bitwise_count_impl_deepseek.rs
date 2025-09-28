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

proof fn lemma_popcount_nonnegative(n: nat)
    ensures
        popcount(n) >= 0,
    decreases n
{
    if n > 0 {
        lemma_popcount_nonnegative(n / 2);
    }
}

proof fn lemma_abs_spec_positive_if_nonzero(x: i32)
    ensures
        x != 0 ==> abs_spec(x) > 0,
{
}

spec fn abs_u32(x: i32) -> u32
    ensures
        abs_u32(x) == abs_spec(x),
{
    if x >= 0 { x as u32 } else { (-x) as u32 }
}

proof fn lemma_abs_u32_equiv(x: i32)
    ensures
        abs_u32(x) == abs_spec(x),
{
}

proof fn lemma_popcount_u32_to_nat(n: u32)
    ensures
        popcount(n as nat) == n.count_ones() as nat,
    decreases n
{
    if n > 0 {
        lemma_popcount_u32_to_nat(n / 2);
    }
}

proof fn lemma_cast_nat_equivalence(val: u32)
    ensures
        (val as nat) == (val as u32) as nat,
{
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
    /* code modified by LLM (iteration 5): Fixed ghost code compilation error by moving count conversion to proof context */
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == popcount(abs_spec(x@[j])),
            forall|j: int| 0 <= j < i ==> x@[j] == 0 ==> result@[j] == 0,
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
        decreases x.len() - i
    {
        let abs_val: u32 = if x[i] >= 0 { x[i] as u32 } else { (-x[i]) as u32 };
        proof { lemma_abs_u32_equiv(x[i]); }
        let count = abs_val.count_ones();
        proof {
            lemma_popcount_u32_to_nat(abs_val);
            lemma_cast_nat_equivalence(count);
            assert(count as nat == popcount(abs_val as nat));
            let count_nat: nat = count as nat;
            result = result.push(count_nat);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}