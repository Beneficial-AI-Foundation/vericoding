spec fn Sum(xs: Seq<int>) -> int {
    if xs.len() == 0 { 0 } else { Sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] }
}

pub fn SumArray(xs: &[int]) -> (s: int)
    ensures(s == Sum(xs@))
{
}