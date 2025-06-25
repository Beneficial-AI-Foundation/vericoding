pub fn ToCharArray(s: &str) -> (a: Vec<char>)
    ensures(a.len() == s.len())
    ensures(forall|i: usize| 0 <= i < s.len() ==> a[i] == s.chars().nth(i).unwrap())
{
}