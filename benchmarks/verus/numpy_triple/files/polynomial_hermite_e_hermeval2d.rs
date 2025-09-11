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

fn hermeval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> exists|hermite_basis: FnSpec(nat, int) -> int|
            (forall|t: int| hermite_basis(0nat, t) == 1) &&
            (c.len() > 0 ==> forall|t: int| hermite_basis(1nat, t) == t) &&
            (forall|i: nat, t: int| i + 1 < c.len() ==> 
                hermite_basis(i + 2, t) == t * hermite_basis(i + 1, t) - (i as int + 1) * hermite_basis(i, t)),
{
    assume(false);
    unreached()
}

}
fn main() {}