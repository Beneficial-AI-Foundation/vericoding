pub fn find_smallest(s: &[i32]) -> (min: i32)
    requires s.len() > 0
    ensures forall|i: usize| 0 <= i < s.len() ==> min <= s[i]
    ensures exists|i: usize| 0 <= i < s.len() && min == s[i]
{
}