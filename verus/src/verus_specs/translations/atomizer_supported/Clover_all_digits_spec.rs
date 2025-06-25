pub fn allDigits(s: &str) -> (result: bool)
    ensures(result <==> (forall|i: usize| 0 <= i < s.len() ==> "0123456789".contains(s.chars().nth(i).unwrap())))
{
}