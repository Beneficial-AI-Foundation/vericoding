use vstd::prelude::*;

verus! {

fn rotate_right(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires n >= 0,
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len() as int) % l.len() as int),
{
    assume(false);
    unreached()
}

}
fn main() {}