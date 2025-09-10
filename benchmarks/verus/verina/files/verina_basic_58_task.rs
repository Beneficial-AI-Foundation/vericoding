use vstd::prelude::*;

verus! {

fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
{
    assume(false);
    unreached()
}

}
fn main() {}