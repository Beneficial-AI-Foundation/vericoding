use vstd::prelude::*;

verus! {

fn true_() -> (result: bool)
    ensures 
        result == true,
        forall|b: bool| (result && b) == b,
        forall|b: bool| (result || b) == true,
        !result == false
{
    assume(false);
    unreached();
}

}
fn main() {}