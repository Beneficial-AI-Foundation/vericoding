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
/* helper modified by LLM (iteration 5): fixed incorrect lemma call to a valid Verus arithmetic lemma */
proof fn lemma_mod_mul_equiv(i: int, a: int, b: int)
    requires
        b > 0,
    ensures
        (i * a) % b == (i * (a % b)) % b,
{
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(i * a, i * (a / b), b);
}
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
{
    /* code modified by LLM (iteration 5): added proof block to help maintain loop invariant */
    let ghost a_int = a as int;
    let ghost b_int = b as int;
    let ghost c_int = c as int;

    let a_op = a as i32;
    let b_op = b as i32;
    let c_op = c as i32;

    let mut i: i32 = 1;
    while i < b_op
        invariant
            valid_input(a_int, b_int, c_int),
            1 <= i <= b_int,
            forall|j: int| 1 <= j < i as int ==> 
                ((j * (a_int % b_int)) % b_int) != c_int,
        decreases (b_op - i) as nat
    {
        if (i * a_op) % b_op == c_op {
            proof {
                let i_int = i as int;
                lemma_mod_mul_equiv(i_int, a_int, b_int);
                assert(is_solvable(a_int, b_int, c_int));
            }
            return "YES".to_string();
        }
        proof {
            lemma_mod_mul_equiv(i as int, a_int, b_int);
        }
        i = i + 1;
    }

    proof {
        assert(!is_solvable(a_int, b_int, c_int));
    }
    return "NO".to_string();
}
// </vc-code>


}

fn main() {}