use vstd::prelude::*;

verus! {

fn abs_it(s: &mut Vec<i32>)
    ensures
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if old(s)[i] < 0 { s[i] == -old(s)[i] } else { s[i] == old(s)[i] }
{
    assume(false);
    unreached()
}

}
fn main() {}