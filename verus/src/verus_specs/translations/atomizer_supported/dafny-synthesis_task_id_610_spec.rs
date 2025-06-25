pub fn remove_element(s: &[i32], k: usize) -> Vec<i32>
    requires(k < s.len())
    ensures(|result: Vec<i32>| result.len() == s.len() - 1)
    ensures(|result: Vec<i32>| forall|i: usize| 0 <= i < k ==> result[i] == s[i])
    ensures(|result: Vec<i32>| forall|i: usize| k <= i < result.len() ==> result[i] == s[i + 1])
{
}