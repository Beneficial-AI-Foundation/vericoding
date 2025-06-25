spec fn sum(xs: Seq<int>) -> int {
    if xs.len() == 0 { 0 } else { sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] }
}

pub fn sum_array(xs: &[int]) -> (s: int)
    ensures(s == sum(xs@))
{
}