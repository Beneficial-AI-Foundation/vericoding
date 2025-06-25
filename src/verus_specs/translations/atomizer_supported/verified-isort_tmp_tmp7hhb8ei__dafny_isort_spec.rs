use vstd::prelude::*;

verus! {

spec fn sorted(a: Seq<nat>) -> bool {
    true // TODO
}

pub fn Isort(a: &mut Vec<nat>)
    ensures sorted(a@)
{
}

}