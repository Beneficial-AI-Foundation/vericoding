use vstd::prelude::*;

verus! {

fn longest_prefix(a: &[i32], b: &[i32]) -> (i: usize)
    ensures 
        i <= a.len() && i <= b.len(),
        a@.subrange(0, i as int) == b@.subrange(0, i as int),
        i < a.len() && i < b.len() ==> a[i as int] != b[i as int]
{
    assume(false);
    unreached()
}

}
fn main() {}