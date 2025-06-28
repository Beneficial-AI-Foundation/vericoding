use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumcheck(s: Vec<int>, n: nat) -> int
    recommends n <= s.len()
    decreases n
{
    if n == 0 {
        0
    } else {
        s[(n - 1) as int] + sumcheck(s, n - 1)
    }
}

proof fn sumcheck_step(s: Vec<int>, i: nat)
    requires 
        i < s.len()
    ensures 
        sumcheck(s, i + 1) == s[i as int] + sumcheck(s, i)
{
    // The proof follows from the definition of sumcheck
    // When we expand sumcheck(s, i + 1):
    // sumcheck(s, i + 1) = s[(i + 1) - 1] + sumcheck(s, (i + 1) - 1)
    //                    = s[i] + sumcheck(s, i)
}

fn sum(s: Vec<int>) -> (a: int)
    requires
        s.len() > 0
    ensures
        sumcheck(s, s.len()) == a
{
    let mut total = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            total == sumcheck(s, i as nat)
    {
        proof {
            // We need to prove that i is within bounds before calling sumcheck_step
            assert(i < s.len());
            sumcheck_step(s, i as nat);
            // After the lemma, we know: sumcheck(s, (i as nat) + 1) == s[i as int] + sumcheck(s, i as nat)
        }
        
        total = total + s[i];
        i = i + 1;
        
        // The invariant is maintained because:
        // new total = old total + s[old i]
        //           = sumcheck(s, old i as nat) + s[old i as int]  [by loop invariant]  
        //           = sumcheck(s, (old i as nat) + 1)             [by sumcheck_step lemma]
        //           = sumcheck(s, new i as nat)                   [since new i = old i + 1]
    }
    
    total
}

}