// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_gt(n: i32, a: &Vec<i32>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> n > a[i]
}
// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures result == (forall|i: int| 0 <= i < a.len() ==> n > a[i]),
// </vc-spec>
// <vc-code>
{
    let mut res: bool = true;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            res == (forall|j: int| 0 <= j < i as int ==> n > a[j]),
        decreases (a.len() - i) as int
    {
        let ai = a[i];
        res = res && n > ai;
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}