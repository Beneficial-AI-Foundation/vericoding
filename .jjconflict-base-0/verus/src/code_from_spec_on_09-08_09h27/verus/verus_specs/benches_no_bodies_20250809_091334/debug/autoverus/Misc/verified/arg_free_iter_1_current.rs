use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd() -> int
    ensures result % 2 == 1
{
    1
}
}