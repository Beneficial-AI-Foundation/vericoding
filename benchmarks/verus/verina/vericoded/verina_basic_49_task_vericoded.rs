// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(x: i32) -> bool {
    x % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn noop() -> bool { true }
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
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            forall|j: int| 0 <= j < i as int ==> !is_odd(a[j]),
        decreases (n - i) as int
    {
        if a[i] % 2 != 0 {
            proof {
                assert(is_odd(a[i as int]));
            }
            return Some(i);
        } else {
            i = i + 1;
        }
    }
    proof {
        assert(i == n);
    }
    None
}
// </vc-code>

}
fn main() {}