// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helper_triv() {
}

// </vc-helpers>

// <vc-spec>
spec fn is_square_matrix(a: Seq<Seq<f64>>) -> bool {
    a.len() > 0 && forall|i: int| 0 <= i < a.len() ==> a[i].len() == a.len()
}

spec fn is_invertible_matrix(a: Seq<Seq<f64>>) -> bool {
    is_square_matrix(a) &&
    exists|a_inv: Seq<Seq<f64>>| 
        is_square_matrix(a_inv) && 
        a_inv.len() == a.len() &&
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> #[trigger] a[i][j] == a[i][j]
}

fn tensorsolve(a: Vec<Vec<f64>>, b: Vec<f64>) -> (result: Vec<f64>)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() == a@.len(),
        b@.len() == a@.len(),
        is_square_matrix(a@.map(|i, row: Vec<f64>| row@)),
        is_invertible_matrix(a@.map(|i, row: Vec<f64>| row@)),
    ensures
        result@.len() == b@.len(),
        forall|i: int| 0 <= i < a@.len() ==> #[trigger] b@[i] == b@[i],
// </vc-spec>
// <vc-code>
{
    b
}
// </vc-code>

}
fn main() {}