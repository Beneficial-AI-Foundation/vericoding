use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd() -> (result: int)
    ensures result % 2 == 1
{
    /* code modified by LLM (iteration 2): Convert literal 1 to int type to fix type mismatch */
    1int
}
}