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
/* helper modified by LLM (iteration 5): removed while loops from proof functions and made them recursive */
spec fn first_even_index(a: Seq<i32>, start: int) -> (i: int)
    recommends start >= 0
    ensures i >= start,
            (i < a.len() ==> is_even(a[i]) && forall|k: int| start <= k < i ==> is_odd(a[k])),
            (i == a.len() ==> forall|k: int| start <= k < a.len() ==> is_odd(a[k]))
{
    if start < a.len() {
        if is_even(a[start]) {
            start
        } else {
            first_even_index(a, start + 1)
        }
    } else {
        a.len()
    }
}

spec fn first_odd_index(a: Seq<i32>, start: int) -> (j: int)
    recommends start >= 0
    ensures j >= start,
            (j < a.len() ==> is_odd(a[j]) && forall|k: int| start <= k < j ==> is_even(a[k])),
            (j == a.len() ==> forall|k: int| start <= k < a.len() ==> is_even(a[k]))
{
    if start < a.len() {
        if is_odd(a[start]) {
            start
        } else {
            first_odd_index(a, start + 1)
        }
    } else {
        a.len()
    }
}

proof fn lemma_find_first_even_exists(a: Seq<i32>) -> (i: int)
    requires
        a.len() > 0,
        exists|x: int| 0 <= x < a.len() && is_even(a[x])
    ensures
        0 <= i < a.len(),
        is_even(a[i]),
        forall|k: int| 0 <= k < i ==> is_odd(a[k])
{
    let candidate = first_even_index(a, 0);
    assert(candidate < a.len()) by {
        assert(forall|k: int| 0 <= k < candidate ==> is_odd(a[k]));
        assert(exists|x: int| 0 <= x < a.len() && is_even(a[x]));
    };
    candidate
}

proof fn lemma_find_first_odd_exists(a: Seq<i32>) -> (j: int)
    requires
        a.len() > 0,
        exists|x: int| 0 <= x < a.len() && is_odd(a[x])
    ensures
        0 <= j < a.len(),
        is_odd(a[j]),
        forall|k: int| 0 <= k < j ==> is_even(a[k])
{
    let candidate = first_odd_index(a, 0);
    assert(candidate < a.len()) by {
        assert(forall|k: int| 0 <= k < candidate ==> is_even(a[k]));
        assert(exists|x: int| 0 <= x < a.len() && is_odd(a[x]));
    };
    candidate
}
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
/* code modified by LLM (iteration 5): simplified implementation using proof function results */
{
    let s = a@;
    
    proof {
        let i = lemma_find_first_even_exists(s);
        let j = lemma_find_first_odd_exists(s);
        assert(0 <= i < a.len() && is_even(s[i]));
        assert(0 <= j < a.len() && is_odd(s[j]));
        assert(forall|k: int| 0 <= k < i ==> is_odd(s[k]));
        assert(forall|k: int| 0 <= k < j ==> is_even(s[k]));
    }
    
    let idx_even = proof {
        let i = lemma_find_first_even_exists(s);
        i as usize
    };
    
    let idx_odd = proof {
        let j = lemma_find_first_odd_exists(s);
        j as usize
    };
    
    a[idx_even] - a[idx_odd]
}
// </vc-code>

}
fn main() {}