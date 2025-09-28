// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 6 && forall|i: int| 0 <= i < 6 ==> 'a' <= #[trigger] s[i] <= 'z'
}

spec fn is_coffee_like(s: Seq<char>) -> bool 
recommends valid_input(s)
{
    s[2] == s[3] && s[4] == s[5]
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_consistency_check(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        is_coffee_like(s) == (s[2] == s[3] && s[4] == s[5]),
{
    // The spec function is_coffee_like is defined exactly as s[2] == s[3] && s[4] == s[5]
}

proof fn lemma_yes_implies_coffee_like(result: Seq<char>)
    requires
        result =~= seq!['Y', 'e', 's'] || result =~= seq!['N', 'o'],
    ensures
        result =~= seq!['Y', 'e', 's'] ==> result[0] == 'Y' && result[1] == 'e' && result[2] == 's',
{
}

proof fn lemma_no_implies_not_coffee_like(result: Seq<char>)
    requires
        result =~= seq!['Y', 'e', 's'] || result =~= seq!['N', 'o'],
    ensures
        result =~= seq!['N', 'o'] ==> result[0] == 'N' && result[1] == 'o',
{
}
/* helper modified by LLM (iteration 5): Added lemmas for string content verification */
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: String)
    requires 
        valid_input(s@)
    ensures 
        result@ =~= seq!['Y', 'e', 's'] || result@ =~= seq!['N', 'o'],
        is_coffee_like(s@) <==> result@ =~= seq!['Y', 'e', 's']
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed implementation with proper verification */
    let third = s[2];
    let fourth = s[3];
    let fifth = s[4];
    let sixth = s[5];
    
    proof {
        lemma_consistency_check(s@);
    }
    
    let result = if third == fourth && fifth == sixth {
        String::from_str("Yes")
    } else {
        String::from_str("No")
    };
    
    proof {
        if third == fourth && fifth == sixth {
            lemma_yes_implies_coffee_like(result@);
        } else {
            lemma_no_implies_not_coffee_like(result@);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}