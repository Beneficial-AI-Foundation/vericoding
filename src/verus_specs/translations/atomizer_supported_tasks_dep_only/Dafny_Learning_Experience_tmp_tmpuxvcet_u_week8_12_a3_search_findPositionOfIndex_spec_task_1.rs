pub fn FindPositionOfElement(a: &[i32], Element: usize, n1: usize, s1: &[i32]) -> (Position: i32, Count: usize)
    requires
        n1 == s1.len() && 0 <= n1 <= a.len(),
        forall|i: usize| 0 <= i < s1.len() ==> a[i] == s1[i],
    ensures |result|
        result.0 == -1 || result.0 >= 1,
        s1.len() != 0 && result.0 >= 1 ==> exists|i: usize| 0 <= i < s1.len() && s1[i] == Element,
{
}