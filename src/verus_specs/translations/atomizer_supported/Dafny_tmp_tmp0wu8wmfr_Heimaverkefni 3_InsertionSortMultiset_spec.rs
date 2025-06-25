pub fn search(s: Seq<int>, x: int) -> (k: int)
    requires(
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
    )
    ensures(|k: int|
        0 <= k <= s.len() &&
        (forall|i: int| 0 <= i < k ==> s[i] <= x) &&
        (forall|i: int| k <= i < s.len() ==> s[i] >= x) &&
        (forall|z: int| s.subrange(0, k).contains(z) ==> z <= x) &&
        (forall|z: int| s.subrange(k, s.len() as int).contains(z) ==> z >= x) &&
        s == s.subrange(0, k) + s.subrange(k, s.len() as int)
    )
{
}

pub fn sort(m: Multiset<int>) -> (r: Seq<int>)
    ensures(|r: Seq<int>|
        r.to_multiset() == m &&
        (forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q])
    )
{
}