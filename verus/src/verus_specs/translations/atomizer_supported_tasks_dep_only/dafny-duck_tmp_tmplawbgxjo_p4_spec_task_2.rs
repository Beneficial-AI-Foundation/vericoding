use vstd::prelude::*;

verus! {

pub fn single(x: &[int], y: &[int]) -> (b: Vec<int>)
    requires(x.len() > 0)
    requires(y.len() > 0)
    ensures(b@ == x@ + y@)
{
}

pub fn main()
{
}

}