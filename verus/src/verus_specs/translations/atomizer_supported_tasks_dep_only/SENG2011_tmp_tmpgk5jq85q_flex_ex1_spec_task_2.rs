// sums from index 0 -> i - 1
// ATOM 
// sums from index 0 -> i - 1
spec fn sumcheck(s: &[int], i: int) -> int
    decreases i
{
    requires(0 <= i <= s.len());
    if i == 0 { 0 } else { s[i - 1] + sumcheck(s, i - 1) }
}

// returns sum of array
// SPEC 

// returns sum of array
pub fn sum(s: &[int]) -> (a: int)
    requires(s.len() > 0)
    ensures(sumcheck(s, s.len() as int) == a)
{
}

// SPEC 

pub fn main() {
}