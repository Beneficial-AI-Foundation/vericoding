spec fn strict_sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

pub fn mcontained(v: &[int], w: &[int], n: usize, m: usize) -> (b: bool)
    requires(
        n <= m && n >= 0,
        strict_sorted(v@),
        strict_sorted(w@),
        v.len() >= n && w.len() >= m,
    )
    ensures(|b: bool| 
        b == forall|k: int| 0 <= k < n ==> w@.subrange(0, m as int).contains(v@[k])
    )
{
}