use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumcheck(s: Vec<int>, n: int) -> int
    recommends 0 <= n <= s.len()
    decreases n
{
    if n <= 0 {
        0
    } else {
        s[n - 1] + sumcheck(s, n - 1)
    }
}

fn sum(s: Vec<int>) -> (a: int)
    requires
        s.len() > 0
    ensures
        sumcheck(s, s.len()) == a
{
    let mut total = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            total == sumcheck(s, i as int)
    {
        total = total + s[i];
        i = i + 1;
    }
    
    total
}

}