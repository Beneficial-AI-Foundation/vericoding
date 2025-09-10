use vstd::prelude::*;

verus! {

spec fn product_of_non_nan_elements(a: Seq<f32>) -> f32 {
    arbitrary()
}

fn nanprod(a: Vec<f32>) -> (result: f32)
    ensures result == product_of_non_nan_elements(a@)
{
    assume(false);
    unreached();
}

}
fn main() {}