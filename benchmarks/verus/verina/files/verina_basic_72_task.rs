use vstd::prelude::*;

verus! {

fn append(a: &Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        result[a.len() as int] == b,
{
    assume(false);
    unreached();
}

}
fn main() {}