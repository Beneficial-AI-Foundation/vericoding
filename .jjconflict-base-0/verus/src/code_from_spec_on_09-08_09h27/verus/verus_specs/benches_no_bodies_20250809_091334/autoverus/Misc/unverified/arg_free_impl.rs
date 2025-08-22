use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd() -> (result: int)
    ensures result % 2 == 1
{
    /* code modified by LLM (iteration 4): Convert integer literal to int type using int constructor */
    int(1)
}
}