// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn online_max(a: &Vec<i8>, x: usize) -> (result: (i8, usize))
    requires
        a.len() > 0,
        x < a.len(),
    ensures
        ({
            let (m, p) = result;
            x <= p && p < a.len()
            && (forall|i: int| 0 <= i < x ==> a[i] as int <= m as int)
            && (exists|i: int| 0 <= i < x && a[i] as int == m as int)
            && ((p < a.len() - 1) ==> (exists|i: int| x <= i <= p && a[i] as int > m as int))
            && ((forall|i: int| x <= i < a.len() ==> a[i] as int <= m as int) ==> p == a.len() - 1)
        })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}