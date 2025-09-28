// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_brother_numbers(a: int, b: int) -> bool {
    1 <= a <= 3 && 1 <= b <= 3 && a != b
}

spec fn late_brother(a: int, b: int) -> int
    recommends valid_brother_numbers(a, b)
{
    6 - a - b
}

spec fn is_valid_result(a: int, b: int, result: int) -> bool {
    valid_brother_numbers(a, b) ==> 
        (1 <= result <= 3 && result != a && result != b)
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_late_brother_different(a: int, b: int)
    requires
        valid_brother_numbers(a, b)
    ensures
        late_brother(a, b) != a,
        late_brother(a, b) != b
{
}

proof fn lemma_late_brother_range(a: int, b: int)
    requires
        valid_brother_numbers(a, b)
    ensures
        1 <= late_brother(a, b) <= 3
{
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_brother_numbers(a as int, b as int)
    ensures 
        is_valid_result(a as int, b as int, result as int) &&
        result as int == late_brother(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_late_brother_different(a as int, b as int);
        lemma_late_brother_range(a as int, b as int);
    }
    
    let sum = a + b;
    let result = 6 - sum;
    
    result
}
// </vc-code>


}

fn main() {}