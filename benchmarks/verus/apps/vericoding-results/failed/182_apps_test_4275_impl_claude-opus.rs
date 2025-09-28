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
    /* code modified by LLM (iteration 5): Use new_strlit to create strings from literals */
    let result = if s[2] == s[3] && s[4] == s[5] {
        let yes_str = new_strlit("Yes");
        assert(yes_str@ =~= seq!['Y', 'e', 's']);
        assert(is_coffee_like(s@));
        yes_str
    } else {
        let no_str = new_strlit("No");
        assert(no_str@ =~= seq!['N', 'o']);
        assert(!is_coffee_like(s@));
        no_str
    };
    result
}
// </vc-code>


}

fn main() {}