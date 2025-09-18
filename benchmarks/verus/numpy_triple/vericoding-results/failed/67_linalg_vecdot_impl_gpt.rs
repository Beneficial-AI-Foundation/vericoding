// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn dot_range(x1: Seq<i32>, x2: Seq<i32>, start: nat, end: nat) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        x1[start] as int * x2[start] as int + dot_range(x1, x2, start + 1, end)
    }
}

proof fn dot_range_full_equals_spec(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == x2.len()
    ensures dot_range(x1, x2, 0, x1.len()) == dot_product_spec(x1, x2)
    decreases x1.len()
{
    if x1.len() == 0 {
    } else {
        dot_range_full_equals_spec(x1.skip(1), x2.skip(1));
    }
}

proof fn dot_product_comm(x1: Seq<i32>, x2: Seq<i32>)
    ensures x1.len() == x2.len() ==> dot_product_spec(x1, x2) == dot_product_spec(x2, x1)
    decreases x1.len()
{
    if x1.len() == 0 || x1.len() != x2.len() {
    } else {
        dot_product_comm(x1.skip(1), x2.skip(1));
    }
}
// </vc-helpers>

// <vc-spec>
spec fn dot_product_spec(x1: Seq<i32>, x2: Seq<i32>) -> int
    decreases x1.len()
{
    if x1.len() == 0 || x1.len() != x2.len() {
        0
    } else {
        x1[0] * x2[0] + dot_product_spec(x1.skip(1), x2.skip(1))
    }
}

fn vecdot(x1: Vec<i32>, x2: Vec<i32>) -> (result: i32)
    requires x1.len() == x2.len(),
    ensures 
        result as int == dot_product_spec(x1@, x2@),
        result as int == dot_product_spec(x2@, x1@)
// </vc-spec>
// <vc-code>
{
    let n = x1.len();
    let mut i: usize = 0;
    let mut acc: int = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            i <= n,
            acc == dot_range(x1@, x2@, 0, i as nat)
    {
        acc = acc + (x1[i] as int) * (x2[i] as int);
        i = i + 1;
    }
    proof {
        dot_range_full_equals_spec(x1@, x2@);
        dot_product_comm(x1@, x2@);
    }
    let result_i32: i32 = acc as i32;
    result_i32
}
// </vc-code>

}
fn main() {}