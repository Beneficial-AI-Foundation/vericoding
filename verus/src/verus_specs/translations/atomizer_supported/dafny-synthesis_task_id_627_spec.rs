pub fn smallest_missing_number(s: Seq<int>) -> (v: int)
    requires(
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    ),
    requires(
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    ),
    ensures(|v: int|
        0 <= v
    ),
    ensures(|v: int|
        !(s.contains(v))
    ),
    ensures(|v: int|
        forall|k: int| 0 <= k < v ==> s.contains(k)
    ),
{
}