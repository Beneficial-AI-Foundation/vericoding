spec fn sum(a: &[int], i: int) -> int
    recommends 0 <= i < a.len()
{
    a[i] + if i == 0 { 0 } else { sum(a, i - 1) }
}

pub fn cumsum(a: &[int], b: &mut [int])
    requires(a.len() == b.len() && a.len() > 0)
    ensures(forall|i: int| 0 <= i < a.len() ==> b[i] == sum(a, i))
{
}