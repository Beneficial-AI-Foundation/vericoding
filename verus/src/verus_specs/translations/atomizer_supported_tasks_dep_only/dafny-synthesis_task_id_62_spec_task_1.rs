pub fn find_smallest(s: &[i32]) -> (min: i32)
    requires
        s.len() > 0,
    ensures |min: i32|
        forall|i: usize| 0 <= i < s.len() ==> min <= s[i as int],
    ensures |min: i32|
        exists|i: usize| 0 <= i < s.len() && min == s[i as int],
{
}