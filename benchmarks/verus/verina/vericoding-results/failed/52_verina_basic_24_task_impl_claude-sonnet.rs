// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof mode lemmas and exec functions */
exec fn is_even_exec(n: i32) -> bool {
    n % 2 == 0
}

exec fn is_odd_exec(n: i32) -> bool {
    n % 2 != 0
}

proof fn lemma_even_odd_properties(n: i32)
    ensures
        is_even(n) == (n % 2 == 0),
        is_odd(n) == (n % 2 != 0),
        is_even(n) <==> !is_odd(n)
{}

proof fn lemma_first_even_exists(a: &Vec<i32>, first_even_idx: usize)
    requires
        a.len() > 1,
        first_even_idx < a.len(),
        is_even(a[first_even_idx as int]),
        forall|k: int| 0 <= k < first_even_idx ==> is_odd(a[k as int])
    ensures
        exists|i: int| 0 <= i < a.len() && is_even(a[i as int]) && i == first_even_idx
{}

proof fn lemma_first_odd_exists(a: &Vec<i32>, first_odd_idx: usize)
    requires
        a.len() > 1,
        first_odd_idx < a.len(),
        is_odd(a[first_odd_idx as int]),
        forall|k: int| 0 <= k < first_odd_idx ==> is_even(a[k as int])
    ensures
        exists|j: int| 0 <= j < a.len() && is_odd(a[j as int]) && j == first_odd_idx
{}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &Vec<i32>) -> (result: i32)
    requires 
        a.len() > 1,
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a.len() &&
            is_even(a[i as int]) && is_odd(a[j as int]) &&
            result == a[i as int] - a[j as int] &&
            (forall|k: int| 0 <= k < i ==> is_odd(a[k as int])) &&
            (forall|k: int| 0 <= k < j ==> is_even(a[k as int]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using exec mode functions for runtime checks */
    let mut first_even_idx: usize = 0;
    let mut first_odd_idx: usize = 0;
    
    // Find first even number
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> is_odd(a[k as int]),
            exists|x: int| 0 <= x < a.len() && is_even(a[x as int])
    {
        if is_even_exec(a[i]) {
            first_even_idx = i;
            break;
        }
        i += 1;
    }
    
    // Find first odd number
    let mut j = 0;
    while j < a.len()
        invariant
            j <= a.len(),
            forall|k: int| 0 <= k < j ==> is_even(a[k as int]),
            exists|x: int| 0 <= x < a.len() && is_odd(a[x as int])
    {
        if is_odd_exec(a[j]) {
            first_odd_idx = j;
            break;
        }
        j += 1;
    }
    
    proof {
        lemma_first_even_exists(a, first_even_idx);
        lemma_first_odd_exists(a, first_odd_idx);
    }
    
    a[first_even_idx] - a[first_odd_idx]
}
// </vc-code>

}
fn main() {}