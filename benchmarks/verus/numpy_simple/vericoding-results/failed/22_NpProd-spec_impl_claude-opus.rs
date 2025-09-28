// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_prod_spec_helper_bounds(a: Seq<i32>, start: int, finish: int)
    requires
        0 <= start <= finish,
        finish <= a.len(),
    ensures
        prod_spec_helper(a, start, finish) == if start >= finish { 1 } else { a[start] * prod_spec_helper(a, start + 1, finish) },
    decreases finish - start
{
    if start >= finish {
        // Base case: trivially true by definition
    } else {
        // Recursive case: also true by definition
        lemma_prod_spec_helper_bounds(a, start + 1, finish);
    }
}

proof fn lemma_prod_contains_zero(a: Seq<i32>, start: int, finish: int, zero_idx: int)
    requires
        0 <= start <= finish,
        finish <= a.len(),
        start <= zero_idx < finish,
        a[zero_idx] == 0,
    ensures
        prod_spec_helper(a, start, finish) == 0,
    decreases finish - start
{
    if start >= finish {
        // Contradiction: start < finish by precondition
        assert(false);
    } else if start == zero_idx {
        // a[start] == 0, so product is 0
        assert(a[start] == 0);
        assert(prod_spec_helper(a, start, finish) == a[start] * prod_spec_helper(a, start + 1, finish));
        assert(prod_spec_helper(a, start, finish) == 0 * prod_spec_helper(a, start + 1, finish));
        assert(prod_spec_helper(a, start, finish) == 0);
    } else {
        // zero_idx is in [start+1, finish)
        lemma_prod_contains_zero(a, start + 1, finish, zero_idx);
        assert(prod_spec_helper(a, start + 1, finish) == 0);
        assert(prod_spec_helper(a, start, finish) == a[start] * prod_spec_helper(a, start + 1, finish));
        assert(prod_spec_helper(a, start, finish) == a[start] * 0);
        assert(prod_spec_helper(a, start, finish) == 0);
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
    let mut result: i32 = 1;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result == prod_spec_helper(a@, 0, i as int),
    {
        result = result * a[i];
        i = i + 1;
    }
    
    result
}

fn prod_array(a: Vec<i32>, start: usize, finish: usize) -> (result: i32)
    requires
        start <= finish,
        finish <= a.len(),
    ensures result == prod_array_spec(a@, start as int, finish as int)
{
    let mut result: i32 = 1;
    let mut i: usize = start;
    
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

proof fn prod_theorem(a: Vec<i32>)
    requires a.len() > 0,
    ensures
        prod_spec(a@) == prod_array_spec(a@, 0, a.len() as int),
        forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> prod_spec(a@) == 0,
{
    // First part: prod_spec equals prod_array_spec
    assert(prod_spec(a@) == prod_spec_helper(a@, 0, a@.len() as int));
    assert(prod_array_spec(a@, 0, a.len() as int) == prod_spec_helper(a@, 0, a@.len() as int));
    assert(prod_spec(a@) == prod_array_spec(a@, 0, a.len() as int));
    
    // Second part: if there's a zero, product is zero
    assert forall|i: int| 0 <= i < a.len() && a[i] == 0 implies prod_spec(a@) == 0 by {
        if 0 <= i < a.len() && a[i] == 0 {
            lemma_prod_contains_zero(a@, 0, a.len() as int, i);
            assert(prod_spec_helper(a@, 0, a.len() as int) == 0);
            assert(prod_spec(a@) == 0);
        }
    }
}
// </vc-code>


}
fn main() {}