use vstd::prelude::*;

verus! {

fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
{
    assume(false);
    unreached()
}

}
fn main() {}