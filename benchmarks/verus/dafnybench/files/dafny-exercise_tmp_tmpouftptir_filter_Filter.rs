use vstd::prelude::*;

verus! {

fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
{
    assume(false);
    unreached()
}

}
fn main() {}