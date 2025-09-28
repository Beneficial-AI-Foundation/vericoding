// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= x <= 200
}

spec fn can_have_exactly_cats(a: int, b: int, x: int) -> bool {
    a <= x <= a + b
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_string_yes_equals_seq()
    ensures "YES"@ =~= seq!['Y', 'E', 'S']
{
    assert("YES"@[0] == 'Y');
    assert("YES"@[1] == 'E');
    assert("YES"@[2] == 'S');
    assert("YES"@.len() == 3);
}

proof fn lemma_string_no_equals_seq()
    ensures "NO"@ =~= seq!['N', 'O']
{
    assert("NO"@[0] == 'N');
    assert("NO"@[1] == 'O');
    assert("NO"@.len() == 2);
}

/* helper modified by LLM (iteration 5): fixed syntax error by using proper not-equal operator */
proof fn lemma_string_sequences_different()
    ensures seq!['Y', 'E', 'S'] !== seq!['N', 'O']
{
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8) -> (result: String)
    requires valid_input(a as int, b as int, x as int)
    ensures result@ =~= seq!['Y', 'E', 'S'] <==> can_have_exactly_cats(a as int, b as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed ghost keyword and used proper arithmetic */
    let sum = a as int + b as int;
    let has_cats = a <= x && x <= sum as i8;
    
    if has_cats {
        proof {
            lemma_string_yes_equals_seq();
        }
        "YES".to_string()
    } else {
        proof {
            lemma_string_no_equals_seq();
            lemma_string_sequences_different();
        }
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}