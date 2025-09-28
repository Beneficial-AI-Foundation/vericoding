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
/* helper modified by LLM (iteration 5): fixed compilation error by using String::from_str */
fn make_yes_string() -> (res: String)
    ensures res@ == seq!['Y', 'e', 's']
{
    String::from_str("Yes")
}

/* helper modified by LLM (iteration 5): fixed compilation error by using String::from_str */
fn make_no_string() -> (res: String)
    ensures res@ == seq!['N', 'o']
{
    String::from_str("No")
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
{
    /* code modified by LLM (iteration 5): no logic change, using fixed helpers */
    if s[2] == s[3] && s[4] == s[5] {
        make_yes_string()
    } else {
        make_no_string()
    }
}
// </vc-code>


}

fn main() {}