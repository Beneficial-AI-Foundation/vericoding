pub fn reverse(a: &[char]) -> Vec<char>
    requires(a.len() > 0)
    ensures(|result: Vec<char>| result.len() == a.len())
    ensures(|result: Vec<char>| forall|i: usize| 0 <= i < a.len() ==> result[i] == a[a.len() - i - 1])
{
}

pub fn main()
{
}