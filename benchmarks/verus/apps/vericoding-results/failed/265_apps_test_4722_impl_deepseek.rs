// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100
}

spec fn distribution_possible(a: int, b: int) -> bool {
    a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mod_3_zero(a: int)
    ensures
        a % 3 == 0 ==> distribution_possible(a, 0),
        a % 3 == 0 ==> distribution_possible(0, a)
{
}

proof fn lemma_mod_3_one(a: int)
    ensures
        a % 3 == 1 ==> distribution_possible(a, 2),
        a % 3 == 1 ==> distribution_possible(2, a)
{
}

proof fn lemma_mod_3_two(a: int)
    ensures
        a % 3 == 2 ==> distribution_possible(a, 1),
        a % 3 == 2 ==> distribution_possible(1, a)
{
}

proof fn lemma_mod_3_sum(a: int, b: int)
    ensures
        (a + b) % 3 == 0 ==> distribution_possible(a, b)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int)
    ensures 
        result@ == seq!['P', 'o', 's', 's', 'i', 'b', 'l', 'e'] <==> distribution_possible(a as int, b as int),
        result@ == seq!['P', 'o', 's', 's', 'i', 'b', 'l', 'e'] || result@ == seq!['I', 'm', 'p', 'o', 's', 's', 'i', 'b', 'l', 'e']
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix Vec construction using from_iter */
    let possible_bytes = &[80, 111, 115, 115, 105, 98, 108, 101];
    let impossible_bytes = &[73, 109, 112, 111, 115, 115, 105, 98, 108, 101];
    
    if a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0 {
        String::from_utf8(Vec::from_iter(possible_bytes.iter().cloned())).unwrap()
    } else {
        String::from_utf8(Vec::from_iter(impossible_bytes.iter().cloned())).unwrap()
    }
}
// </vc-code>


}

fn main() {}