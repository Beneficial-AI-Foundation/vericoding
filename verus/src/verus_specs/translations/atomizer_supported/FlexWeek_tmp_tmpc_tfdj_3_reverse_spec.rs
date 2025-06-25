pub fn reverse(a: &[char]) -> Vec<char>
    requires(a.len() > 0)
    ensures(|result: Vec<char>| a.len() == result.len())
    ensures(|result: Vec<char>| forall|k: usize| 0 <= k < a.len() ==> result[k] == a[(a.len()-1) - k])
{
}

pub fn main() {
}