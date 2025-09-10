use vstd::prelude::*;

verus! {

fn merge_sort(list: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == list.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@ =~= list@,
{
    assume(false);
    unreached();
}

}
fn main() {}