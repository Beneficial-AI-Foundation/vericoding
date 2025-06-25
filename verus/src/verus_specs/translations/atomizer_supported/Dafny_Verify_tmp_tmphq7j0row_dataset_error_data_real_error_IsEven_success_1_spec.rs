spec fn even(n: int) -> bool
    recommends n >= 0
{
    if n == 0 { true } else { !even(n - 1) }
}

pub fn is_even(n: int) -> (r: bool)
    requires n >= 0
    ensures r <==> even(n)
{
}