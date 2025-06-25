pub fn smallest_missing_number(s: &Vec<i32>) -> i32
    requires(
        forall|i: usize, j: usize| 0 <= i < j < s.len() ==> s[i] <= s[j]
    )
    requires(
        forall|i: usize| 0 <= i < s.len() ==> s[i] >= 0
    )
    ensures(|v: i32|
        0 <= v &&
        !s.contains(v) &&
        forall|k: i32| 0 <= k < v ==> s.contains(k)
    )
{
}