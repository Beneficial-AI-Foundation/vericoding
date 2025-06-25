pub fn smallest_missing_number(s: &Vec<int>) -> (v: int)
    requires(
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    )
    requires(
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
    )
    ensures(|v: int|
        0 <= v &&
        !(s.contains(v)) &&
        forall|k: int| 0 <= k < v ==> s.contains(k)
    )
{
}