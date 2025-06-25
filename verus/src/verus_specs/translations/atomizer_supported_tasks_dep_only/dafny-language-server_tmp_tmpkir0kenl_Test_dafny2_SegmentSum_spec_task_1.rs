spec fn Sum(a: Seq<int>, s: int, t: int) -> int
    recommends 0 <= s <= t <= a.len()
{
    if s == t { 0 } else { Sum(a, s, t-1) + a[t-1] }
}

pub fn MaxSegSum(a: Seq<int>) -> (k: int, m: int)
    ensures 
        0 <= k <= m <= a.len(),
        forall|p: int, q: int| 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= Sum(a, k, m)
{
}