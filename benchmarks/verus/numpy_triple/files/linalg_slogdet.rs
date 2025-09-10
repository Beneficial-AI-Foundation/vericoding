use vstd::prelude::*;

verus! {

fn slogdet(a: Vec<Vec<f32>>) -> (result: (f32, f32))
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a.len(),
    ensures ({
        let (sign, logabsdet) = result;
        (sign == -1.0f32 || sign == 0.0f32 || sign == 1.0f32)
    }),
{
    assume(false);
    unreached()
}

}
fn main() {}