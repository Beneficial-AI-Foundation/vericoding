// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn eigvalsh(a: Vec<Vec<i8>>) -> (eigenvals: Vec<i8>)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == a.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i][j] == a[j][i],
    ensures
        eigenvals.len() == a.len(),
        /* Eigenvalues are in ascending order */
        forall|i: int, j: int| 0 <= i < j < eigenvals.len() ==> eigenvals[i] <= eigenvals[j],
        /* Identity matrix has all eigenvalues equal to 1 */
        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> 
            a[i][j] as int == (if i == j { 1int } else { 0int })) ==> 
            (forall|i: int| 0 <= i < eigenvals.len() ==> eigenvals[i] as int == 1int),
        /* Zero matrix has all eigenvalues equal to 0 */
        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i][j] as int == 0int) ==> 
            (forall|i: int| 0 <= i < eigenvals.len() ==> eigenvals[i] as int == 0int)
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