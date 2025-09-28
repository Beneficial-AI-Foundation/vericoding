// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 2
}

spec fn satisfies_constraint(x: int, n: int, k: int) -> bool {
    x > 0 && k > 0 && (x / k) * (x % k) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add satisfies_constraint helper in ghost */
spec fn satisfies_constraint_ghost_u8(x: u8, n: u8, k: u8) -> bool {
    x > 0 && k > 0 && ((x / k) * (x % k)) == n
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result > 0,
        satisfies_constraint(result as int, n as int, k as int),
        forall|x: int| #[trigger] satisfies_constraint(x, n as int, k as int) ==> result as int <= x
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix type casting issues in satisfies_constraint call by introducing ghost helper */
{
    let mut x: u8 = n * k;
    let initial_x: u8 = n * k;

    while x >= 1
        invariant
            x >= 1,
            x <= initial_x,
            forall|val: int|
                #![trigger satisfies_constraint(val, n as int, k as int)]
                (x as int) < val && (val <= initial_x as int) ==> !satisfies_constraint(val, n as int, k as int)
        decreases x
    {
        // Use the spec function with appropriate casting
        if satisfies_constraint_ghost_u8(x, n as u8, k as u8) {
            return x as i8;
        }
        x = x - 1;
    }

    // This part should be unreachable given the problem constraints and proof obligations.
    // Since we're proving correctness, this line represents an impossible state if proofs hold.
    // We add an unreachable! here, and the ensures clause will verify that a valid x is indeed found.
    unreachable!();
}
// </vc-code>


}

fn main() {}