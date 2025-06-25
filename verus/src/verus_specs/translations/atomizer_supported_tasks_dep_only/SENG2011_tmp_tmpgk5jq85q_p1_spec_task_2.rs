pub fn reverse(a: &[char]) -> Vec<char>
    requires(a.len() > 0)
    ensures(|result: Vec<char>| a.len() == result.len())
    ensures(|result: Vec<char>| forall|x: usize| 0 <= x < a.len() ==> result[x] == a[a.len() - x - 1])
{
}

pub fn main()
{
}