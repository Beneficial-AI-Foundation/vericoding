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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and postcondition verification */
    let mut i: i8 = 1;
    let a_mod_b = (a % b) as i8;
    
    while i < b
        invariant
            1 <= i <= b,
            1 <= a <= 100,
            1 <= b <= 100,
            0 <= c < b,
            a_mod_b == (a % b) as i8,
            forall|j: int| 1 <= j < i as int ==> #[trigger] ((j * (a as int % b as int)) % b as int) != c as int,
            i < b ==> is_solvable(a as int, b as int, c as int) == exists|j: int| i as int <= j < b as int && #[trigger] ((j * (a as int % b as int)) % b as int) == c as int,
        decreases b - i
    {
        let product = (i as int * a_mod_b as int) as i8;
        let result_mod = (product % b) as i8;
        
        if result_mod == c {
            assert(((i as int * (a as int % b as int)) % b as int) == c as int);
            assert(is_solvable(a as int, b as int, c as int));
            return "YES".to_string();
        }
        i = i + 1;
    }
    
    assert(i == b);
    assert(forall|j: int| 1 <= j < b as int ==> #[trigger] ((j * (a as int % b as int)) % b as int) != c as int);
    assert(!is_solvable(a as int, b as int, c as int));
    return "NO".to_string();
}
// </vc-code>


}

fn main() {}