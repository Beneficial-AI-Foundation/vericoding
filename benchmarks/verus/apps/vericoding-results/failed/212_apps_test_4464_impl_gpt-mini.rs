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
/* helper modified by LLM (iteration 5): assert existence witness implies is_solvable with trigger */
proof fn exists_witness_implies_solvable(a: int, b: int, c: int, i: int)
    requires
        1 <= i < b,
        ((i * (a % b)) % b) == c,
    ensures
        is_solvable(a, b, c),
{
    assert(exists|j: int| 1 <= j < b && #[trigger] ((j * (a % b)) % b) == c);
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
/* code modified by LLM (iteration 5): search for a solution and maintain invariant with trigger on modulo term */
{
    let A = a as i32;
    let B = b as i32;
    let C = c as i32;
    let mut i: i32 = 1;
    let mut found: bool = false;
    let mut found_i: i32 = 0;
    while i < B && !found
        invariant
            1 <= i as int <= b as int,
            (!found) ==> (forall|j: int| 1 <= j < i as int ==> #[trigger] ((j * (a as int % b as int)) % b as int) != c as int),
        decreases
            b as int - i as int
    {
        let prod = (i * (A % B)) % B;
        if prod == C {
            found = true;
            found_i = i;
        } else {
            i = i + 1;
        }
    }
    if found {
        proof {
            let j: int = found_i as int;
            let Aint: int = a as int;
            let Bint: int = b as int;
            let Cint: int = c as int;
            assert(1 <= j < Bint);
            assert(((j * (Aint % Bint)) % Bint) == Cint);
            exists_witness_implies_solvable(Aint, Bint, Cint, j);
        }
        return "YES".to_string();
    } else {
        proof {
            assert(i as int >= b as int);
            let Bint: int = b as int;
            let Aint: int = a as int;
            let Cint: int = c as int;
            assert(forall|j: int| 1 <= j < Bint ==> #[trigger] ((j * (Aint % Bint)) % Bint) != Cint);
        }
        return "NO".to_string();
    }
}

// </vc-code>


}

fn main() {}