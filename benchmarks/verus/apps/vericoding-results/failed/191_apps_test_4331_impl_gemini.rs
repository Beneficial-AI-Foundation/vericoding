// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    100 <= n <= 999
}

spec fn contains_seven(n: int) -> bool
    recommends valid_input(n)
{
    (n % 10) == 7 || ((n / 10) % 10) == 7 || (n / 100) == 7
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == "Yes\n"@ || result == "No\n"@
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Fixed compilation error by using correct path and types for math lemmas] */
proof fn lemma_check_equiv_spec(n: i8)
    requires
        valid_input(n as int),
    ensures
        (n % 10 == 7 || (n / 10) % 10 == 7 || n / 100 == 7) <==> contains_seven(n as int),
{
    vstd::arithmetic::div_mod::lemma_rem_is(n as int, 10);
    vstd::arithmetic::div_mod::lemma_div_is(n as int, 10);
    let d = n / 10;
    vstd::arithmetic::div_mod::lemma_rem_is(d as int, 10);
    vstd::arithmetic::div_mod::lemma_div_is(n as int, 100);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures 
        valid_output(result@) &&
        ((result@ == "Yes\n"@) <==> contains_seven(n as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [retaining correct logic which should now verify with the fixed helper] */
    proof {
        lemma_check_equiv_spec(n);
    }
    if n % 10 == 7 || (n / 10) % 10 == 7 || n / 100 == 7 {
        vec!['Y', 'e', 's', '\n']
    } else {
        vec!['N', 'o', '\n']
    }
}
// </vc-code>


}

fn main() {}