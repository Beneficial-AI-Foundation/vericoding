pub fn min_second_value_first(s: &[Vec<i32>]) -> (firstOfMinSecond: i32)
    requires 
        s.len() > 0,
        forall|i: usize| 0 <= i < s.len() ==> s[i].len() >= 2,
    ensures |firstOfMinSecond: i32|
        exists|i: usize| 0 <= i < s.len() && firstOfMinSecond == s[i][0] && 
            (forall|j: usize| 0 <= j < s.len() ==> s[i][1] <= s[j][1])
{
}