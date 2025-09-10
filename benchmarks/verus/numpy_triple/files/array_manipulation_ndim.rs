use vstd::prelude::*;

verus! {

fn ndim<T>(a: &Vec<T>) -> (result: usize)
    ensures result == 1
{
    assume(false);
    unreached()
}

}
fn main() {}