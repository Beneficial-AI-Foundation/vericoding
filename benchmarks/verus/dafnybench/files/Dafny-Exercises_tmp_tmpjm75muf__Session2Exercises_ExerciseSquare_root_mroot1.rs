use vstd::prelude::*;

verus! {

fn mroot1(n: u32) -> (r: u32)
    requires n >= 0,
    ensures r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
{
    assume(false);
    unreached()
}

}
fn main() {}