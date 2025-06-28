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
        s[(n - 1) as int] + sumcheck(s, n - 1)
    }
}

proof fn sumcheck_step(s: Vec<int>, i: int)
    requires 
        0 <= i < s.len()
    ensures 
        sumcheck(s, i + 1) == s[i] + sumcheck(s, i)
{
    // The proof follows from the definition of sumcheck
    // When we expand sumcheck(s, i + 1):
    // sumcheck(s, i + 1) = s[(i + 1) - 1] + sumcheck(s, (i + 1) - 1)
    //                    = s[i] + sumcheck(s, i)
    // This matches exactly what we need to prove
}

fn sum(s: Vec<int>) -> (a: int)
    requires
        s.len() > 0
    ensures
        sumcheck(s, s.len() as int) == a
{
    let mut total = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            total == sumcheck(s, i as int)
    {
        proof {
            sumcheck_step(s, i as int);
        }
        
        total = total + s[i];
        i = i + 1;
    }
    
    total
}

}