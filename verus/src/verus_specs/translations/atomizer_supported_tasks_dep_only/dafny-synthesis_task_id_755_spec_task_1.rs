// ATOM 
pub fn MinPair(s: Seq<int>) -> (r: int)
    requires(s.len() == 2)
    ensures(|r| s[0] <= s[1] <==> r == s[0])
    ensures(|r| s[0] > s[1] ==> r == s[1])
{
}

// ATOM 
pub fn min(s: Seq<int>) -> (r: int)
    requires(s.len() >= 2)
    ensures(|r| forall|i: int| 0 <= i < s.len() ==> r <= s[i])
{
}

// SPEC 
pub fn SecondSmallest(s: &[int]) -> (secondSmallest: int)
    requires(s.len() >= 2)
    requires(exists|i: usize, j: usize| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] == min(s@) && s[j] != s[i])
    ensures(|secondSmallest| exists|i: usize, j: usize| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] == min(s@) && s[j] == secondSmallest)
    ensures(|secondSmallest| forall|k: usize| 0 <= k < s.len() && s[k] != min(s@) ==> s[k] >= secondSmallest)
{
}