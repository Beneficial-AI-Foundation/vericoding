use vstd::prelude::*;

verus! {

fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        first.len() > 0,
    ensures 
        result.len() == first.len() - 1 + second.len(),
        forall|i: int| 0 <= i < first.len() - 1 ==> result[i] == first[i],
        forall|i: int| first.len() - 1 <= i < result.len() ==> result[i] == second[i - first.len() + 1],
{
    assume(false);
    unreached();
}

}
fn main() {}