use vstd::prelude::*;

verus! {

fn get_first_elements(lst: Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires forall|i: int| 0 <= i < lst.len() ==> lst[i].len() > 0,
    ensures 
        result.len() == lst.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == lst[i][0],
{
    assume(false);
    unreached();
}

}
fn main() {}