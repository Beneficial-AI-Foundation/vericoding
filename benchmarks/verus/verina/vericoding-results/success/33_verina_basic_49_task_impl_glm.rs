// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(x: i32) -> bool {
    x % 2 != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_first_odd(a: &Vec<i32>) -> (result: Option<usize>)
    requires a.len() > 0,
    ensures
        match result {
            Some(idx) => idx < a.len() && is_odd(a[idx as int]) &&
                forall|j: int| 0 <= j < idx ==> !is_odd(a[j]),
            None => forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i]),
        },
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            forall|j: int| 0 <= j < i as int ==> !is_odd(a[j]),
        decreases (a.len() - i) as nat,
    {
        if a[i] % 2 != 0 {
            return Some(i);
        }
        i += 1;
    }
    return None;
}
// </vc-code>

}
fn main() {}