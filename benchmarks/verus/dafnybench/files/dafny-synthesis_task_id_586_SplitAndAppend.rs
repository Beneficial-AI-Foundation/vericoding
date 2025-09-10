use vstd::prelude::*;

verus! {

fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
{
    assume(false);
    unreached()
}

}
fn main() {}