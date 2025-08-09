use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd() -> (result: int)
    ensures result % 2 == 1
{
    /* code modified by LLM (iteration 3): Use plain integer literal 1, which will be inferred as int type */
    1
}
}