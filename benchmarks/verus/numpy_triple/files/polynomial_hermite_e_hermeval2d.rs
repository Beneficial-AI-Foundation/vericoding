// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn hermite_e_basis(n: nat, x: int) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        x
    } else {
        x * hermite_e_basis((n-1) as nat, x) - (n-1) as int * hermite_e_basis((n-2) as nat, x)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermeval2d(x: Vec<i8>, y: Vec<i8>, c: Vec<Vec<i8>>) -> (result: Vec<i8>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] hermite_e_basis(0nat, x[k] as int) == 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}