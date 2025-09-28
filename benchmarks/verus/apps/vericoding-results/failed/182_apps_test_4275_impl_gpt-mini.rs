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
/* helper modified by LLM (iteration 5): prove String::from_str("Yes") equals sequence */
proof fn string_from_str_yes()
    ensures
        String::from_str("Yes")@ =~= seq!['Y','e','s'],
{
    assert(String::from_str("Yes")@ =~= seq!['Y','e','s']);
}

/* helper modified by LLM (iteration 5): prove String::from_str("No") equals sequence */
proof fn string_from_str_no()
    ensures
        String::from_str("No")@ =~= seq!['N','o'],
{
    assert(String::from_str("No")@ =~= seq!['N','o']);
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
    /* code modified by LLM (iteration 5): return "Yes" if coffee-like else "No" */
    if is_coffee_like(s@) {
        let r = String::from_str("Yes");
        proof {
            string_from_str_yes();
        }
        r
    } else {
        let r = String::from_str("No");
        proof {
            string_from_str_no();
        }
        r
    }
}

// </vc-code>


}

fn main() {}