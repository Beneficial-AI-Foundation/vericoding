use vstd::prelude::*;

verus! {

spec fn F() -> int {
    29
}

pub fn M() -> (r: int)
    ensures r == 29
{
}

pub fn Caller() {
}

pub fn M() -> (r: int)
    ensures r == 29
{
}

}