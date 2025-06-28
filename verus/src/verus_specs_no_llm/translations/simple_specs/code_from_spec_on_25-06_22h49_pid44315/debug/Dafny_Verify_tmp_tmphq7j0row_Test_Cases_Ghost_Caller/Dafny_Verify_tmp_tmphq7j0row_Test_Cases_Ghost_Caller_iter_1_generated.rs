use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn M() -> (r: i32) 
    ensures r == 29
{
    29
}

//ATOM
spec fn F() -> int {
    29
}

// SPEC
fn Caller() -> (r: i32)
    ensures r == 29
{
    29
}

}