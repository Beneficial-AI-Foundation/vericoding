// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Sum of integers over finite indices */
pub open spec fn int_sum(n: nat, f: spec_fn(int) -> int) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        f((n - 1) as int) + int_sum((n - 1) as nat, f)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ifftn(a: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    requires 
        a.len() > 0,
        a.len() < usize::MAX,
        forall|i: int| 0 <= i < a.len() ==> a[i as int].len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i as int].len() < usize::MAX,
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i as int].len() == a[j as int].len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int].len() == a[0].len(),
        forall|i: int, j: int| #[trigger] result[i as int][j as int] == 0 || 
            (0 <= i < result.len() && 0 <= j < result[i as int].len()),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}