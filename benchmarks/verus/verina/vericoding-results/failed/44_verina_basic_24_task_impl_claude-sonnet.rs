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
/* helper modified by LLM (iteration 5): added bounds checking and overflow verification helpers */
fn is_even_exec(n: i32) -> (result: bool)
    ensures result == is_even(n)
{
    n % 2 == 0
}

fn is_odd_exec(n: i32) -> (result: bool)
    ensures result == is_odd(n)
{
    n % 2 != 0
}

fn safe_subtract(a: i32, b: i32) -> (result: i32)
    requires a as i64 - b as i64 >= i32::MIN as i64 && a as i64 - b as i64 <= i32::MAX as i64
    ensures result == a - b
{
    a - b
}

fn can_subtract_safely(a: i32, b: i32) -> (result: bool)
    ensures result == (a as i64 - b as i64 >= i32::MIN as i64 && a as i64 - b as i64 <= i32::MAX as i64)
{
    let diff = a as i64 - b as i64;
    diff >= i32::MIN as i64 && diff <= i32::MAX as i64
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
    /* code modified by LLM (iteration 5): fix type mismatch by converting usize to int for spec function calls */
    let mut first_even_idx: usize = 0;
    let mut first_odd_idx: usize = 0;
    
    // Find first even number
    while first_even_idx < a.len()
        invariant
            first_even_idx <= a.len(),
            forall|k: int| 0 <= k < first_even_idx ==> is_odd(a[k]),
        decreases a.len() - first_even_idx
    {
        if is_even_exec(a[first_even_idx]) {
            break;
        }
        first_even_idx += 1;
    }
    
    // Find first odd number
    while first_odd_idx < a.len()
        invariant
            first_odd_idx <= a.len(),
            forall|k: int| 0 <= k < first_odd_idx ==> is_even(a[k]),
        decreases a.len() - first_odd_idx
    {
        if is_odd_exec(a[first_odd_idx]) {
            break;
        }
        first_odd_idx += 1;
    }
    
    // Verify bounds before subtraction
    assert(first_even_idx < a.len());
    assert(first_odd_idx < a.len());
    
    let even_val = a[first_even_idx];
    let odd_val = a[first_odd_idx];
    
    // Check overflow conditions
    assert(can_subtract_safely(even_val, odd_val));
    
    let result = safe_subtract(even_val, odd_val);
    
    proof {
        assert(is_even_exec(a[first_even_idx]) == is_even(a[first_even_idx as int]));
        assert(is_even(a[first_even_idx as int]));
        assert(is_odd_exec(a[first_odd_idx]) == is_odd(a[first_odd_idx as int]));
        assert(is_odd(a[first_odd_idx as int]));
        assert(result == a[first_even_idx as int] - a[first_odd_idx as int]);
        assert(forall|k: int| 0 <= k < first_even_idx ==> is_odd(a[k]));
        assert(forall|k: int| 0 <= k < first_odd_idx ==> is_even(a[k]));
    }
    
    result
}
// </vc-code>

}
fn main() {}