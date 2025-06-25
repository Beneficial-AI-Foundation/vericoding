use vstd::prelude::*;

verus! {

spec fn power(a: int, n: int) -> int
    recommends 0 <= n;

pub fn A8Q1(y0: int, x: int) -> (z: int)
    requires(y0 >= 0)
    ensures(z == power(x, y0))
{
    todo!()
}

}