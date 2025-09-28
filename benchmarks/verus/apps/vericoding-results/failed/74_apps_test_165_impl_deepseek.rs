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
proof fn lemma_max3_properties(a: int, b: int, c: int)
    ensures
        max3(a, b, c) >= a,
        max3(a, b, c) >= b,
        max3(a, b, c) >= c,
        max3(a, b, c) == a || max3(a, b, c) == b || max3(a, b, c) == c,
{
    if a >= b && a >= c {
        assert(max3(a, b, c) == a);
    } else if b >= c {
        assert(max3(a, b, c) == b);
    } else {
        assert(max3(a, b, c) == c);
    }
}

fn int_to_string_impl(n: int) -> (s: String)
    requires n >= 0
    ensures s@ == int_to_string_spec(n)
{
    if n == 0int {
        String::from("0")
    } else {
        let mut num: int = n;
        let mut chars = Vec::new();
        while num > 0int
            invariant
                num >= 0,
                num > 0 ==> chars@.len() > 0
            decreases num
        {
            let digit: int = num % 10int;
            num = num / 10int;
            chars.push((b'0' as int + digit as int) as u8 as char);
        }
        chars.reverse();
        String::from(chars.into_iter().collect::<String>())
    }
}

fn count_missed_meals(input: &str) -> (count: int)
    requires valid_input(input@)
    ensures count == calculate_missed_meals(input@)
{
    let mut missed: int = 0int;
    let mut consecutive_absences: int = 0int;
    let chars: Vec<char> = input.chars().collect();
    let mut i: int = 0;
    while i < chars@.len() as int
        invariant
            i >= 0 && i <= chars@.len() as int,
            missed >= 0,
            consecutive_absences >= 0,
            missed == calculate_missed_meals(chars@.subrange(0, i as usize)),
            consecutive_absences == 0 || (i > 0 && chars@[(i as usize) - 1] == '0'),
        decreases chars@.len() as int - i
    {
        if chars[i as usize] == '0' {
            consecutive_absences = consecutive_absences + 1int;
            if consecutive_absences >= 3int {
                missed = missed + 1int;
            }
        } else {
            consecutive_absences = 0int;
        }
        i = i + 1int;
    }
    missed
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
requires valid_input(input@)
ensures result@ == int_to_string_spec(calculate_missed_meals(input@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implement main logic */
    let missed_meals = count_missed_meals(input);
    let result_string = int_to_string_impl(missed_meals);
    result_string
}
// </vc-code>


}

fn main() {}