use vstd::prelude::*;

verus! {
   

fn f(x: i32) -> (r: i32)
    ensures r == x + 1
{
    x + 1
}

proof fn lemma_f_monotonic(x: int)
    ensures f(x as i32) >= x
{
    // Unfolding or reasoning about f directly:
    assert(f(x as i32) == x + 1);
}

fn main(){}

}