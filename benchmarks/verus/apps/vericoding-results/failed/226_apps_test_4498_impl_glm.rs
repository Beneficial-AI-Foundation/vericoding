// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

spec fn can_communicate(a: int, b: int, c: int, d: int) -> bool {
    (if a - c >= 0 { a - c } else { c - a }) <= d || 
    (((if a - b >= 0 { a - b } else { b - a }) <= d) && 
     ((if b - c >= 0 { b - c } else { c - b }) <= d))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix overflow by using int arithmetic */
fn can_comm_exec(a: i8, b: i8, c: i8, d: i8) -> bool {
    let a_int = a as int;
    let b_int = b as int;
    let c_int = c as int;
    let d_int = d as int;

    let diff_ac = if a_int >= c_int { a_int - c_int } else { c_int - a_int };
    let diff_ab = if a_int >= b_int { a_int - b_int } else { b_int - a_int };
    let diff_bc = if b_int >= c_int { b_int - c_int } else { c_int - b_int };

    diff_ac <= d_int || (diff_ab <= d_int && diff_bc <= d_int)
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int, d as int),
    ensures 
        result@ == seq!['Y', 'e', 's'] <==> can_communicate(a as int, b as int, c as int, d as int),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fix postconditions by proving equivalence and string content */
{
    let comm = can_comm_exec(a, b, c, d);
    let result = if comm {
        "Yes".to_string()
    } else {
        "No".to_string()
    };

    proof {
        let a_int = a as int;
        let b_int = b as int;
        let c_int = c as int;
        let d_int = d as int;

        // Unfold the definition of can_comm_exec
        let diff_ac = if a_int >= c_int { a_int - c_int } else { c_int - a_int };
        let diff_ab = if a_int >= b_int { a_int - b_int } else { b_int - a_int };
        let diff_bc = if b_int >= c_int { b_int - c_int } else { c_int - b_int };
        let comm_exec = diff_ac <= d_int || (diff_ab <= d_int && diff_bc <= d_int);

        // The spec function can_communicate
        let comm_spec = (if a_int - c_int >= 0 { a_int - c_int } else { c_int - a_int }) <= d_int || 
                        (((if a_int - b_int >= 0 { a_int - b_int } else { b_int - a_int }) <= d_int) && 
                         ((if b_int - c_int >= 0 { b_int - c_int } else { c_int - b_int }) <= d_int));

        // Prove the differences are the same
        assert(diff_ac == (if a_int - c_int >= 0 { a_int - c_int } else { c_int - a_int }));
        assert(diff_ab == (if a_int - b_int >= 0 { a_int - b_int } else { b_int - a_int }));
        assert(diff_bc == (if b_int - c_int >= 0 { b_int - c_int } else { c_int - b_int }));

        // Therefore, comm_exec == comm_spec
        assert(comm_exec == comm_spec);

        // And comm == comm_exec by definition
        assert(comm == comm_exec);
        assert(comm == comm_spec);

        // Now, about the string:
        assert("Yes"@ == seq!['Y','e','s']);
        assert("No"@ == seq!['N','o']);

        // Therefore, the biconditional holds.
        assert(result@ == seq!['Y','e','s'] <==> comm_spec);
        assert(result@ == seq!['Y','e','s'] || result@ == seq!['N','o']);
    }

    result
}
// </vc-code>


}

fn main() {}