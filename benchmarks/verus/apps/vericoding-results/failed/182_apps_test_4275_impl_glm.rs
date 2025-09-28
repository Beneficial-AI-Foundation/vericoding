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
/* helper modified by LLM (iteration 5): fix compilation error by naming return value */
fn is_coffee_like_vec(s: Vec<char>) -> (result: bool)
    requires valid_input(s@)
    ensures result == is_coffee_like(s@)
{
    s[2] == s[3] && s[4] == s[5]
}
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
/* code modified by LLM (iteration 5): no change in logic, but updating iteration comment */
{
    let cond = is_coffee_like_vec(s);
    if cond {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}