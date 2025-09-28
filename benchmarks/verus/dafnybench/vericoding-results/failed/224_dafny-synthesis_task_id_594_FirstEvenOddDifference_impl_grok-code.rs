use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>

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
    let len = a.len();
    assert(len >= 2);
    let mut first_even: usize = 0;
    while first_even < len && !is_even(a@[first_even as int] as int) {
        invariant first_even <= len as int;
        invariant forall |k: int| #[trigger] (0 <= k < first_even as int) ==> !is_even(a@[k] as int);
        first_even += 1;
    }
    assert(first_even < len);
    assert(forall |k: int| #[trigger] (0 <= k < first_even as int) ==> is_odd(a@[k] as int));
    let mut first_odd: usize = 0;
    while first_odd < len && !is_odd(a@[first_odd as int] as int) {
        invariant first_odd <= len as int;
        invariant forall |k: int| #[trigger] (0 <= k < first_odd as int) ==> !is_odd(a@[k] as int);
        first_odd += 1;
    }
    assert(first_odd < len);
    assert(forall |k: int| #[trigger] (0 <= k < first_odd as int) ==> is_even(a@[k] as int));
    (a@[first_even as int] as int - a@[first_odd as int] as int) as i32
}
// </vc-code>

fn main() {
}

}