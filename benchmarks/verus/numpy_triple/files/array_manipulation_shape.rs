use vstd::prelude::*;

verus! {

fn shape<T>(a: &Vec<T>) -> (result: usize)
    ensures result == a.len()
{
    assume(false);
    unreached()
}

}
fn main() {}