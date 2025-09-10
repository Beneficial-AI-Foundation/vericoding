use vstd::prelude::*;

verus! {

fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32),
        (a.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a.len() && a[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32) ==> result == true),
{
    assume(false);
    unreached()
}

}
fn main() {}