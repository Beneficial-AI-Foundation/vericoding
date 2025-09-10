use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;

fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
{
    assume(false);
    unreached()
}

}
fn main() {}