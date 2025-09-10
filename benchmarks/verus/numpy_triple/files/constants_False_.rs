use vstd::prelude::*;

verus! {

fn false_() -> (result: bool)
    ensures 
        result == false,
        forall|b: bool| (result || b) == b,
        forall|b: bool| (result && b) == false,
        result == !true
{
    assume(false);
    unreached();
}

}
fn main() {}