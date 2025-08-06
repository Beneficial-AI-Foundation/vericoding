use vstd::prelude::*;

verus! {
    fn match_strings(s: Vec<char>, p: Vec<char>) -> (b: bool)
        requires s.len() == p.len(),
        ensures b <==> forall|n: int| 0 <= n < s.len() ==> 
            s[n] == p[n] || p[n] == '?'
    {
    return false;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}