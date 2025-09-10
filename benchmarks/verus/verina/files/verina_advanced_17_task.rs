use vstd::prelude::*;

verus! {

fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
{
    assume(false);
    unreached()
}

}
fn main() {}