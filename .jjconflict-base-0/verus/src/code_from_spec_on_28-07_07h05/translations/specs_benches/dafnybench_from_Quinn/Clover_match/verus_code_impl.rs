use vstd::prelude::*;

verus! {
    //IMPL match_strings
    fn match_strings(s: Vec<char>, p: Vec<char>) -> (b: bool)
        requires s.len() == p.len(),
        ensures b <==> forall|n: int| 0 <= n < s.len() ==> 
            s[n] == p[n] || p[n] == '?'
    {
        let mut i = 0;
        /* code modified by LLM (iteration 1): updated loop condition and invariants to ensure bounds checking */
        while i < s.len()
            invariant 
                0 <= i <= s.len(),
                s.len() == p.len(),
                forall|n: int| 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
            decreases s.len() - i
        {
            /* code modified by LLM (iteration 1): bounds are now guaranteed by loop condition and invariant */
            if s[i] != p[i] && p[i] != '?' {
                return false;
            }
            i += 1;
        }
        return true;
    }
}

fn main() {}