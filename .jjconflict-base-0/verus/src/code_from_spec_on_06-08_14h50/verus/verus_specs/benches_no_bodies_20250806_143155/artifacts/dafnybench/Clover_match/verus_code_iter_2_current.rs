use vstd::prelude::*;

verus! {
    fn match_strings(s: Vec<char>, p: Vec<char>) -> (b: bool)
        requires s.len() == p.len(),
        ensures b <==> forall|n: int| 0 <= n < s.len() ==> 
            s[n] == p[n] || p[n] == '?'
    {
        let mut i = 0;
        while i < s.len()
            invariant 
                0 <= i <= s.len(),
                forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
            /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
            decreases s.len() - i
        {
            if s[i] != p[i] && p[i] != '?' {
                return false;
            }
            i += 1;
        }
        true
    }
}

fn main() {}