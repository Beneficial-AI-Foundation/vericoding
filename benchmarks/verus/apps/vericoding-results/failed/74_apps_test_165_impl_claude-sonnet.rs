// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c { a }
    else if b >= c { b }
    else { c }
}

spec fn calculate_missed_meals(input: Seq<char>) -> int {
    /* Implementation placeholder for spec function */
    0
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn int_to_string_spec(n: int) -> Seq<char> {
    /* Specification for integer to string conversion */
    seq![]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use vstd string operations instead of chars().collect() */
exec fn count_missed_meals(input: &str) -> (result: usize)
    ensures
        result as int == calculate_missed_meals(input@)
{
    let mut missed: usize = 0;
    let mut i: usize = 0;
    
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            missed as int >= 0
    {
        if input.get_char(i as int) == 'E' {
            missed = missed + 1;
        }
        i = i + 1;
    }
    
    missed
}

exec fn int_to_string(n: usize) -> (result: String)
    ensures
        result@ == int_to_string_spec(n as int)
{
    n.to_string()
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
requires valid_input(input@)
ensures result@ == int_to_string_spec(calculate_missed_meals(input@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use fixed count_missed_meals function */
    let missed = count_missed_meals(input);
    int_to_string(missed)
}
// </vc-code>


}

fn main() {}