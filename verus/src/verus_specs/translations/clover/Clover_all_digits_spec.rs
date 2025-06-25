pub fn allDigits(s: &str) -> (result: bool)
    ensures(result <==> (forall|i: int| 0 <= i < s.len() ==> "0123456789".contains(s[i as usize])))
{
}