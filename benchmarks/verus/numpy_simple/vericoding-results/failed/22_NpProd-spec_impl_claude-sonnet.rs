// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add proof implementation for prod_array helper lemmas */
proof fn prod_spec_helper_range_lemma(a: Seq<i32>, start: int, mid: int, finish: int)
    requires start <= mid <= finish
    ensures prod_spec_helper(a, start, finish) == prod_spec_helper(a, start, mid) * prod_spec_helper(a, mid, finish)
    decreases finish - start
{
    if start >= mid {
        assert(prod_spec_helper(a, start, mid) == 1);
    } else {
        prod_spec_helper_range_lemma(a, start + 1, mid, finish);
    }
}

proof fn prod_spec_helper_zero_lemma(a: Seq<i32>, start: int, finish: int, zero_idx: int)
    requires 
        start <= zero_idx < finish,
        a[zero_idx] == 0
    ensures prod_spec_helper(a, start, finish) == 0
    decreases finish - start
{
    if start == zero_idx {
        assert(prod_spec_helper(a, start, finish) == a[start] * prod_spec_helper(a, start + 1, finish));
        assert(a[start] == 0);
    } else {
        prod_spec_helper_zero_lemma(a, start + 1, finish, zero_idx);
    }
}
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
{
    /* code modified by LLM (iteration 5): implement prod_array function with loop invariant */
    if start == finish {
        return 1;
    }
    
    let mut result = 1;
    let mut i = start;
    
    while i < finish
        invariant
            start <= i <= finish,
            result == prod_spec_helper(a@, start as int, i as int),
    {
        result = result * a[i];
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}