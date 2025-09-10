use vstd::prelude::*;

verus! {

fn linspace(start: f32, stop: f32, num: usize) -> (result: Vec<f32>)
    requires num > 0,
    ensures
        result.len() == num,
        result[0] == start,
        (num == 1 ==> forall|i: int| 0 <= i < num ==> result[i] == start),
        (num > 1 ==> result[num - 1] == stop)
{
    assume(false);
    unreached();
}

}
fn main() {}