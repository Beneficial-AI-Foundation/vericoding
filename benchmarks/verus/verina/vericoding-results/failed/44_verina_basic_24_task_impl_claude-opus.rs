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
/* helper modified by LLM (iteration 5): Added exec_is_even and exec_is_odd functions for runtime evaluation */
fn exec_is_even(n: i32) -> (result: bool)
    ensures result == is_even(n)
{
    n % 2 == 0
}

fn exec_is_odd(n: i32) -> (result: bool)
    ensures result == is_odd(n)
{
    n % 2 != 0
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
{
    /* code modified by LLM (iteration 5): Use checked_sub to handle potential overflow safely */
    let mut first_even: Option<i32> = None;
    let mut first_odd: Option<i32> = None;
    let mut first_even_idx: Option<usize> = None;
    let mut first_odd_idx: Option<usize> = None;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            first_even.is_none() ==> (forall|k: int| 0 <= k < i ==> is_odd(a[k as int])),
            first_even.is_some() ==> first_even_idx.is_some() && 0 <= first_even_idx.unwrap() < i && is_even(a[first_even_idx.unwrap() as int]) && first_even.unwrap() == a[first_even_idx.unwrap() as int] && (forall|m: int| 0 <= m < first_even_idx.unwrap() ==> is_odd(a[m as int])),
            first_odd.is_none() ==> (forall|k: int| 0 <= k < i ==> is_even(a[k as int])),
            first_odd.is_some() ==> first_odd_idx.is_some() && 0 <= first_odd_idx.unwrap() < i && is_odd(a[first_odd_idx.unwrap() as int]) && first_odd.unwrap() == a[first_odd_idx.unwrap() as int] && (forall|m: int| 0 <= m < first_odd_idx.unwrap() ==> is_even(a[m as int])),
        decreases a.len() - i
    {
        if first_even.is_none() && exec_is_even(a[i]) {
            first_even = Some(a[i]);
            first_even_idx = Some(i);
        }
        if first_odd.is_none() && exec_is_odd(a[i]) {
            first_odd = Some(a[i]);
            first_odd_idx = Some(i);
        }
        if first_even.is_some() && first_odd.is_some() {
            proof {
                let ie = first_even_idx.unwrap() as int;
                let io = first_odd_idx.unwrap() as int;
                assert(0 <= ie < a.len() && 0 <= io < a.len());
                assert(is_even(a[ie]) && is_odd(a[io]));
                assert(forall|k: int| 0 <= k < ie ==> is_odd(a[k]));
                assert(forall|k: int| 0 <= k < io ==> is_even(a[k]));
            }
            let result = first_even.unwrap().checked_sub(first_odd.unwrap()).unwrap();
            return result;
        }
        i = i + 1;
    }
    
    assert(first_even.is_some());
    assert(first_odd.is_some());
    proof {
        let ie = first_even_idx.unwrap() as int;
        let io = first_odd_idx.unwrap() as int;
        assert(0 <= ie < a.len() && 0 <= io < a.len());
        assert(is_even(a[ie]) && is_odd(a[io]));
        assert(forall|k: int| 0 <= k < ie ==> is_odd(a[k]));
        assert(forall|k: int| 0 <= k < io ==> is_even(a[k]));
    }
    let result = first_even.unwrap().checked_sub(first_odd.unwrap()).unwrap();
    result
}
// </vc-code>

}
fn main() {}