use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
proof fn lemma_even_odd_diff_helper(a: &[i32], i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
        is_even(a[i] as int),
        is_odd(a[j] as int),
        forall|k: int| 0 <= k < i ==> is_odd(a@[k] as int),
        forall|k: int| 0 <= k < j ==> is_even(a@[k] as int),
    ensures
        true
{
}

proof fn i32_even_to_int_even(x: int)
    ensures (x % 2 == 0) == (is_even(x))
{
    assert(x % 2 == 0);
}

proof fn i32_odd_to_int_odd(x: int)
    ensures (x % 2 != 0) == (is_odd(x))
{
    assert(x % 2 != 0);
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
    let mut first_even_index: usize = 0;
    let mut found_even = false;
    let mut first_odd_index: usize = 0;
    let mut found_odd = false;

    for i in 0..a.len()
        invariant
            0 <= first_even_index <= i <= a.len(),
            found_even ==> (first_even_index <= i && is_even(a@[first_even_index as int] as int) && forall|k: int| 0 <= k < (first_even_index as int) ==> is_odd(a@[k] as int)),
            0 <= first_odd_index <= i <= a.len(),
            found_odd ==> (first_odd_index <= i && is_odd(a@[first_odd_index as int] as int) && forall|k: int| 0 <= k < (first_odd_index as int) ==> is_even(a@[k] as int)),
    {
        if !found_even && (a[i] % 2 == 0) {
            first_even_index = i;
            found_even = true;
            proof {
                i32_even_to_int_even(a@[i as int] as int);
            }
        }
        if !found_odd && (a[i] % 2 != 0) {
            first_odd_index = i;
            found_odd = true;
            proof {
                i32_odd_to_int_odd(a@[i as int] as int);
            }
        }
    }

    proof {
        assert(found_even);
        assert(found_odd);
    }
    
    a[first_even_index] - a[first_odd_index]
}
// </vc-code>

fn main() {
}

}