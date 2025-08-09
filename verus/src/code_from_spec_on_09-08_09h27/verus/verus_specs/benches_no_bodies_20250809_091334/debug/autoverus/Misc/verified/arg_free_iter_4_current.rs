use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd() -> (result: int)
    ensures result % 2 == 1
{
    /* code modified by LLM (iteration 3): use proper int literal syntax */
    1 as int
}
}