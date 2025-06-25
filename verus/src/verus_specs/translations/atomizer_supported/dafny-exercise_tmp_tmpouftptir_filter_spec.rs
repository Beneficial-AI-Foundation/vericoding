use vstd::prelude::*;

verus! {

pub fn Filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
{
}

pub fn TesterFilter()
{
}

}