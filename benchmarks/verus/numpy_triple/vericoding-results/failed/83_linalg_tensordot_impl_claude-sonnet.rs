// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed spec function usage in recursive spec context */
fn dot_product_lemma(a: Seq<i32>, b: Seq<i32>, i: nat, sum: int)
    requires
        i <= a.len(),
        a.len() == b.len(),
    ensures
        sum + dot_product_recursive(a, b, i) == 
            if i == 0 {
                dot_product(a, b)
            } else {
                sum + dot_product_recursive(a, b, i)
            },
    decreases a.len() - i
{
    if i >= a.len() {
        // base case
    } else {
        proof {
            dot_product_lemma(a, b, i + 1, sum + a[i as int] * b[i as int]);
        }
    }
}

fn compute_dot_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: i32)
    requires
        a.len() == b.len(),
    ensures
        result == dot_product(a@, b@),
{
    let mut i: usize = 0;
    let mut sum = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            sum == dot_product_recursive(a@, b@, 0) - dot_product_recursive(a@, b@, i as nat),
    {
        proof {
            dot_product_lemma(a@, b@, i as nat, sum as int);
        }
        sum = sum + a[i] * b[i];
        i = i + 1;
    }
    
    sum
}
// </vc-helpers>

// <vc-spec>
spec fn dot_product_recursive(a: Seq<i32>, b: Seq<i32>, i: nat) -> int
    decreases a.len() - i
{
    if i >= a.len() {
        0
    } else {
        a[i as int] * b[i as int] + dot_product_recursive(a, b, i + 1)
    }
}

spec fn dot_product(a: Seq<i32>, b: Seq<i32>) -> int {
    dot_product_recursive(a, b, 0)
}

fn tensordot(a: Vec<i32>, b: Vec<i32>, axes: usize) -> (result: i32)
    requires 
        a.len() == b.len(),
        axes == 1,
    ensures result == dot_product(a@, b@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper function */
    compute_dot_product(&a, &b)
}
// </vc-code>

}
fn main() {}