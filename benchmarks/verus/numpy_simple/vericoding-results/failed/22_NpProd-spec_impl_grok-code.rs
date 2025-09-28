// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_prod_spec_zero(a: Seq<i32>, start: int, finish: int)
    requires
        start <= finish,
        0 <= start <= finish <= a.len(),
        exists|i: int| start <= i < finish && a[i] == 0
    ensures
        prod_spec_helper(a, start, finish) == 0
    decreases finish - start
{
    if start >= finish {
        // Empty range has no zero, contradiction
    } else if a[start] == 0 {
        // Done
    } else {
        lemma_prod_spec_zero(a, start + 1, finish);
    }
}
/* helper modified by LLM (iteration 5): lemma to prove product is zero if zero in range */
// </vc-helpers>

// <vc-spec>
spec fn prod_spec_helper(a: Seq<i32>, start: int, finish: int) -> int
    decreases finish - start
{
    if start >= finish {
        1
    } else {
        a[start] * prod_spec_helper(a, start + 1, finish)
    }
}

spec fn prod_spec(a: Seq<i32>) -> int {
    prod_spec_helper(a, 0, a.len() as int)
}

spec fn prod_array_spec(a: Seq<i32>, start: int, finish: int) -> int {
    prod_spec_helper(a, start, finish)
}

fn prod(a: Vec<i32>) -> (result: i32)
    ensures result == prod_spec(a@)
{
    // impl-start
    assume(false);
    0
    // impl-end
}

fn prod_array(a: Vec<i32>, start: usize, finish: usize) -> (result: i32)
    requires 
        start <= finish,
        finish <= a.len(),
    ensures result == prod_array_spec(a@, start as int, finish as int)
{
    // impl-start
    assume(false);
    0
    // impl-end
}

proof fn prod_theorem(a: Vec<i32>)
    requires a.len() > 0,
    ensures 
        prod_spec(a@) == prod_array_spec(a@, 0, a.len() as int) &&
        (forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> prod_spec(a@) == 0)
{
    assume(false);
}
// </vc-spec>
// <vc-code>
fn prod(a: Vec<i32>) -> (result: i32)
    ensures result == prod_spec(a@)
{
    /* code modified by LLM (iteration 5): implement prod by calling prod_array */
    prod_array(a, 0, a.len())
}

fn prod_array(a: Vec<i32>, start: usize, finish: usize) -> (result: i32)
    requires 
        start <= finish,
        finish <= a.len()
    ensures result == prod_array_spec(a@, start as int, finish as int)
{
    /* code modified by LLM (iteration 5): implement prod_array using while loop with invariant */
    let mut res = 1;
    let mut i = start;
    while i < finish
        invariant
            start <= i,
            i <= finish,
            res == prod_spec_helper(a@, start as int, i as int)
        decreases finish - i
    {
        res = res * a[i];
        i = i + 1;
    }
    res
}

proof fn prod_theorem(a: Vec<i32>)
    requires a.len() > 0
    ensures 
        prod_spec(a@) == prod_array_spec(a@, 0, a.len() as int) &&
        (forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> prod_spec(a@) == 0)
{
    /* code modified by LLM (iteration 5): implement prod_theorem proving the equivalence and zero case */
    assert forall |i: int| 0 <= i < a@.len() && a@[i] == 0 implies prod_spec(a@) == 0 by {
        lemma_prod_spec_zero(a@, 0, a@.len());
    }
}
// </vc-code>


}
fn main() {}