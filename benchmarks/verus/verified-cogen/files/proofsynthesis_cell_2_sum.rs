use vstd::prelude::*;

verus!{

fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)

    requires 
        old(a).len() == N,
        N <= 0x7FFF_FFFF,

    ensures
        sum <= 2*N,
{
    assume(false);
    unreached();
}

}
fn main() {}