// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 0 <= c < b
}

spec fn is_solvable(a: int, b: int, c: int) -> bool {
    exists|i: int| 1 <= i < b && #[trigger] ((i * (a % b)) % b) == c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes required */
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        (result@ == "YES"@) <==> is_solvable(a as int, b as int, c as int),
        (result@ == "NO"@) || (result@ == "YES"@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by changing comparisons to avoid i8 casts in assertions and using parentheses */{
    let k: i8 = a % b;
    let mut i: i8 = 1;
    while i < b
        invariant
            1 <= i as int <= b as int,
            forall |j: int| 1 <= j < i as int ==> (((j * (k as int)) % (b as int)) != c as int),
        decreases
            b as int - i as int
    {
        let temp: i32 = ((i as i32) * (k as i32)) % (b as i32);
        if temp == c as i32 {
            proof {
                assert((1 <= i as int) && (i as int < b as int));
                assert(((i as int * (k as int)) % (b as int)) == c as int);
                assert(#[trigger] ((i as int) * (a as int % b as int)) % b as int == c as int);
            }
            return "YES".to_string();
        }
        i = i + 1;
    }
    proof {
        assert(forall |j: int| 1 <= j < b as int ==> (((j * (a as int % b as int)) % b as int) != c as int));
    }
    return "NO".to_string();
}
// </vc-code>


}

fn main() {}