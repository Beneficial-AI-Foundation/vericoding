// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma: dot_product equals recursive form */
fn lemma_dot_product_def(a: Seq<i32>, b: Seq<i32>)
    ensures
        dot_product(a, b) == dot_product_recursive(a, b, 0),
{
    proof {
        assert(dot_product(a, b) == dot_product_recursive(a, b, 0));
    }
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
    /* code modified by LLM (iteration 5): use view().len() in invariant and compute in unbounded int to avoid i32 overflow */
    let len: usize = a.len();
    let mut i: usize = 0;
    let mut acc: int = 0;
    while i < len
        invariant
            i <= len,
            len == a.view().len(),
            acc + dot_product_recursive(a@, b@, i as nat) == dot_product(a@, b@),
        decreases len - i
    {
        let av: i32 = a[i];
        let bv: i32 = b[i];
        let prod: int = (av as int) * (bv as int);
        acc = acc + prod;
        i = i + 1;
    }
    let result_int: int = acc;
    proof {
        assert(i == len);
        assert(acc + dot_product_recursive(a@, b@, i as nat) == dot_product(a@, b@));
        assert(dot_product_recursive(a@, b@, i as nat) == 0);
        assert(acc == dot_product(a@, b@));
    }
    result_int as i32
}

// </vc-code>

}
fn main() {}