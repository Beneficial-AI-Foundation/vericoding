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
/* helper modified by LLM (iteration 5): construct constant string "Yes" without using unsupported constructors */
fn yes_string() -> (r: String)
    ensures
        r@ =~= seq!['Y','e','s'],
{
    String::from_seq(seq!['Y','e','s'])
}

/* helper modified by LLM (iteration 5): construct constant string "No" without using unsupported constructors */
fn no_string() -> (r: String)
    ensures
        r@ =~= seq!['N','o'],
{
    String::from_seq(seq!['N','o'])
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
    /* code modified by LLM (iteration 5): compute equality checks and return Yes/No accordingly; prove bounds and spec */
    proof {
        assert(s@.len() == 6);
        assert(s@.len() == s.len() as int);
        assert(2 < s.len());
        assert(3 < s.len());
        assert(4 < s.len());
        assert(5 < s.len());
    }

    let e23 = s[2] == s[3];
    let e45 = s[4] == s[5];

    if e23 && e45 {
        let r = yes_string();
        proof {
            assert(s@[2] == s[2]);
            assert(s@[3] == s[3]);
            assert(s@[4] == s[4]);
            assert(s@[5] == s[5]);
            assert(e23);
            assert(e45);
            assert(s@[2] == s@[3]);
            assert(s@[4] == s@[5]);
            assert(is_coffee_like(s@));
        }
        r
    } else {
        let r = no_string();
        proof {
            assert(s@[2] == s[2]);
            assert(s@[3] == s[3]);
            assert(s@[4] == s[4]);
            assert(s@[5] == s[5]);
            if !e23 {
                assert(s@[2] != s@[3]);
            } else {
                assert(!e45);
                assert(s@[4] != s@[5]);
            }
            assert(!is_coffee_like(s@));
        }
        r
    }
}
// </vc-code>


}

fn main() {}