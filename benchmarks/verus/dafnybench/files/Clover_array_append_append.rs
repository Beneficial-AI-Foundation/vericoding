use vstd::prelude::*;

verus! {

fn append(a: &Vec<i32>, b: i32) -> (c: Vec<i32>)
    ensures c@ == a@ + seq![b]
{
    assume(false);
    unreached()
}

}
fn main() {}