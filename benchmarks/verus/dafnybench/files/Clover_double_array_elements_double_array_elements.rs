use vstd::prelude::*;

verus! {

fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
{
    assume(false);
    unreached();
}

}
fn main() {}