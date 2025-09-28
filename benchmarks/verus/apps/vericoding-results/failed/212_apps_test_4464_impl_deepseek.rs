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
proof fn lemma_modulo_properties(a: int, b: int)
    requires
        b > 0
    ensures
        forall|i: int| 0 <= i < b ==> exists|k: int| #[trigger]((a % b) + i - k * b) == a + i
{
    assert forall|i: int| 0 <= i < b implies exists|k: int| ((a % b) + i - (a / b) * b) == a + i by {
        let k = a / b;
        assert((a % b) + i - k * b == a % b - k * b + i == (a % b - (a / b) * b) + i);
        assert(a == (a / b) * b + a % b);
        assert(a % b - (a / b) * b + i == a - (a / b) * b - (a / b) * b + i);
    };
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
    /* code modified by LLM (iteration 5): Fixed proof and loop implementation */
    proof {
        lemma_solution_exists(a as int, b as int, c as int);
    }
    let mut i: i8 = 1;
    while i < b
        invariant
            1 <= i <= b,
            forall|j: int| 1 <= j < i as int ==> ((j * (a as int % b as int)) % b as int) != c as int,
        decreases (b - i) as int
    {
        if (i * (a % b)) % b == c {
            return "YES".to_string();
        }
        i = i + 1;
    }
    "NO".to_string()
}
// </vc-code>


}

fn main() {}