pub fn IsPalindrome(x: Seq<char>) -> (result: bool)
    ensures(result <==> (forall|i: int| 0 <= i < x.len() ==> x[i] == x[x.len() - i - 1]))
{
}