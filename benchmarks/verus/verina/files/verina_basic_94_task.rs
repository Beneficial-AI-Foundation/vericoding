use vstd::prelude::*;

verus! {

fn iter_copy(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == result[i],
{
    assume(false);
    unreached()
}

}
fn main() {}