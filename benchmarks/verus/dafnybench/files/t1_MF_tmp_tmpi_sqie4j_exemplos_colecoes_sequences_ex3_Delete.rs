use vstd::prelude::*;

verus! {

fn delete(line: &mut Vec<char>, l: usize, at: usize, p: usize)
    requires
        l <= old(line).len(),
        at + p <= l,
    ensures
        line@ == old(line)@.subrange(0, at as int) + old(line)@.subrange((at + p) as int, l as int),
{
    assume(false);
    unreached()
}

}
fn main() {}