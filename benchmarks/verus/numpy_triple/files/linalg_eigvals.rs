use vstd::prelude::*;

verus! {

struct Complex {
    re: f32,
    im: f32,
}

fn eigvals(a: Vec<Vec<f32>>) -> (result: Vec<Complex>)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == a.len(),
    ensures 
        result.len() == a.len(),

        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j ==> #[trigger] a[i][j] == 0.0f32) ==>
        (forall|i: int| #![auto] 0 <= i < a.len() ==> 
            exists|j: int| 0 <= j < result.len() && 
                result[j].re == a[i][i] && result[j].im == 0.0f32),
{
    assume(false);
    unreached()
}

}
fn main() {}