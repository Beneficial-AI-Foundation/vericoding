use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
fn is_even_exec(n: i32) -> (result: bool)
    ensures result == is_even(n as int)
{
    n % 2 == 0
}

fn is_odd_exec(n: i32) -> (result: bool)
    ensures result == is_odd(n as int)
{
    n % 2 != 0
}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &[i32]) -> (diff: i32)
    requires 
        a.len() >= 2,
        exists|i: int| 0 <= i < a.len() && is_even(a[i] as int),
        exists|i: int| 0 <= i < a.len() && is_odd(a[i] as int),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 
            0 <= j < a.len() && 
            is_even(a[i] as int) && 
            is_odd(a[j] as int) && 
            diff == a[i] - a[j] && 
            (forall|k: int| 0 <= k < i ==> is_odd(a[k] as int)) && 
            (forall|k: int| 0 <= k < j ==> is_even(a[k] as int))
// </vc-spec>
// <vc-code>
{
    let mut first_even_idx: usize = 0;
    let mut first_odd_idx: usize = 0;
    let mut found_even = false;
    let mut found_odd = false;
    
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            !found_even ==> forall|k: int| #![auto] 0 <= k < idx ==> is_odd(a[k] as int),
            !found_odd ==> forall|k: int| #![auto] 0 <= k < idx ==> is_even(a[k] as int),
            found_even ==> (
                0 <= first_even_idx < a.len() &&
                is_even(a[first_even_idx as int] as int) &&
                forall|k: int| #![auto] 0 <= k < first_even_idx ==> is_odd(a[k] as int)
            ),
            found_odd ==> (
                0 <= first_odd_idx < a.len() &&
                is_odd(a[first_odd_idx as int] as int) &&
                forall|k: int| #![auto] 0 <= k < first_odd_idx ==> is_even(a[k] as int)
            ),
            idx < a.len() || (found_even && found_odd),
        invariant_except_break
            found_even ==> (
                0 <= first_even_idx <= idx &&
                first_even_idx < a.len()
            ),
            found_odd ==> (
                0 <= first_odd_idx <= idx &&
                first_odd_idx < a.len()
            ),
        ensures
            found_even && found_odd,
            0 <= first_even_idx < a.len(),
            0 <= first_odd_idx < a.len(),
            is_even(a[first_even_idx as int] as int),
            is_odd(a[first_odd_idx as int] as int),
            forall|k: int| #![auto] 0 <= k < first_even_idx ==> is_odd(a[k] as int),
            forall|k: int| #![auto] 0 <= k < first_odd_idx ==> is_even(a[k] as int),
        decreases a.len() - idx
    {
        if !found_even && is_even_exec(a[idx]) {
            first_even_idx = idx;
            found_even = true;
        }
        if !found_odd && is_odd_exec(a[idx]) {
            first_odd_idx = idx;
            found_odd = true;
        }
        
        if found_even && found_odd {
            break;
        }
        
        idx = idx + 1;
    }
    
    proof {
        assert(found_even);
        assert(found_odd);
        assert(0 <= first_even_idx < a.len());
        assert(0 <= first_odd_idx < a.len());
        assert(is_even(a[first_even_idx as int] as int));
        assert(is_odd(a[first_odd_idx as int] as int));
        assert(forall|k: int| #![auto] 0 <= k < first_even_idx ==> is_odd(a[k] as int));
        assert(forall|k: int| #![auto] 0 <= k < first_odd_idx ==> is_even(a[k] as int));
    }
    
    (a[first_even_idx] as i32) - (a[first_odd_idx] as i32)
}
// </vc-code>

fn main() {
}

}