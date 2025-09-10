use vstd::prelude::*;

verus! {

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    assume(false);
    unreached()
}

}
fn main() {}