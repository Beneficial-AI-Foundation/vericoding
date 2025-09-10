use vstd::prelude::*;

verus! {

spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i]@.len() > 0 && all_chars_digit(a[i]@))
{
    assume(false);
    unreached()
}

}
fn main() {}