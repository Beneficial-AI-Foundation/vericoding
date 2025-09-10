use vstd::prelude::*;

verus! {

fn put(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>) -> (result: Vec<f64>)
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind.len() ==> ind[i] < a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < ind.len() ==> result[ind[i] as int] == v[i],
        forall|j: int| 0 <= j < result.len() ==> 
            (forall|i: int| 0 <= i < ind.len() ==> j != ind[i]) ==> result[j] == a[j],
        ind.len() == 0 ==> result@ == a@,
{
    assume(false);
    unreached()
}

}
fn main() {}