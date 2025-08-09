use vstd::prelude::*;

verus! {

// Precondition: strings must have equal length
spec fn match_precond(s: Seq<char>, p: Seq<char>) -> bool {
    s.len() == p.len()
}

// Main function that checks if string s matches pattern p  
// where '?' in pattern can match any character
/* code modified by LLM (iteration 1): changed to spec fn since proof fn cannot contain loops and mutations */
spec fn match_fn(s: Seq<char>, p: Seq<char>) -> bool
    recommends match_precond(s, p)
{
    forall|n: int| 0 <= n < s.len() ==> 
        (s[n] == p[n] || p[n] == '?')
}

// Postcondition specification  
spec fn match_postcond(s: Seq<char>, p: Seq<char>, result: bool) -> bool {
    result <==> forall|n: int| 0 <= n < s.len() ==> 
        (s[n] == p[n] || p[n] == '?')
}

// Implementation function that actually performs the matching
/* code modified by LLM (iteration 1): added implementation function for actual computation */
fn match_impl(s: Vec<char>, p: Vec<char>) -> (result: bool)
    requires match_precond(s@, p@)
    ensures result == match_fn(s@, p@)
    ensures match_postcond(s@, p@, result)
{
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            s@.len() == p@.len(),
            forall|j: int| 0 <= j < i ==> (s@[j] == p@[j] || p@[j] == '?')
    {
        if s[i] != p[i] && p[i] != '?' {
            return false;
        }
        i += 1;
    }
    
    true
}

// Theorem statement (proof omitted as in original Lean code)
/* code modified by LLM (iteration 2): added missing function body with curly braces */
proof fn match_spec_satisfied(s: Vec<char>, p: Vec<char>)
    requires match_precond(s@, p@)
    ensures match_postcond(s@, p@, match_fn(s@, p@))
{
    // The postcondition follows directly from the definition of match_fn
    // since match_postcond(s@, p@, result) is defined as 
    // result <==> forall|n: int| 0 <= n < s.len() ==> (s[n] == p[n] || p[n] == '?')
    // and match_fn returns exactly this condition
}

} // verus!

fn main() {}