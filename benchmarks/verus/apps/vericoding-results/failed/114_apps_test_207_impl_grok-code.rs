// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>) -> bool {
    a.len() >= 1
}

spec fn can_be_divided(a: Seq<int>) -> bool
    recommends valid_input(a)
{
    a.len() % 2 == 1 && a[0] % 2 == 1 && a[a.len() - 1] % 2 == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: String)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        can_be_divided(a@.map(|i, x| x as int)) ==> result@ =~= seq!['Y', 'e', 's'],
        (!can_be_divided(a@.map(|i, x| x as int))) ==> result@ =~= seq!['N', 'o'],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed compilation by avoiding 'as int' in exec code */
{
    let len_odd = a.len() % 2 == 1;
    let first_odd = ((a[0] as i32) % 2 == 1);
    let last_odd = ((a[a.len() - 1] as i32) % 2 == 1);
    let divided = len_odd && first_odd && last_odd;
    if divided {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}