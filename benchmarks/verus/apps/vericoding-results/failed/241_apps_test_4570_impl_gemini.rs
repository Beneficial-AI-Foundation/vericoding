// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    true /* Simplified for now */
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0
}

spec fn split_string_func(s: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['1'], seq!['2'], seq!['3']] /* Simplified for now */
}

spec fn string_to_int_func(s: Seq<char>) -> int {
    if s.len() > 0 && s[0] == '1' { 1 }
    else if s.len() > 0 && s[0] == '2' { 2 }
    else if s.len() > 0 && s[0] == '3' { 3 }
    else { 0 }
}

spec fn int_to_string_func(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else if n == 3 { seq!['3'] }
    else { seq!['0'] }
}

spec fn min_parking_cost(n: int, a: int, b: int) -> int {
    let plan1_cost = n * a;
    let plan2_cost = b;
    if plan1_cost <= plan2_cost { plan1_cost } else { plan2_cost }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no change] */
fn split_string_impl(s: &Seq<char>) -> (parts: Vec<Vec<char>>)
    ensures
        parts.view() == split_string_func(*s),
{
    vec![vec!['1'], vec!['2'], vec!['3']]
}

/* helper modified by LLM (iteration 5): [no change] */
fn string_to_int_impl(s: &Vec<char>) -> (i: i64)
    requires
        is_valid_integer(s.view()),
    ensures
        i as int == string_to_int_func(s.view()),
{
    if s[0] == '1' { 1 }
    else if s[0] == '2' { 2 }
    else if s[0] == '3' { 3 }
    else { 0 }
}

/* helper modified by LLM (iteration 5): [no change] */
fn int_to_string_impl(n: i64) -> (s: Vec<char>)
    ensures
        s.view() == int_to_string_func(n as int),
{
    if n == 0 { vec!['0'] }
    else if n == 1 { vec!['1'] }
    else if n == 2 { vec!['2'] }
    else if n == 3 { vec!['3'] }
    else { vec!['0'] }
}

/* helper modified by LLM (iteration 5): [no change] */
fn min_parking_cost_impl(n: i64, a: i64, b: i64) -> (cost: i64)
    ensures
        cost as int == min_parking_cost(n as int, a as int, b as int),
{
    let plan1_cost = n * a;
    let plan2_cost = b;
    if plan1_cost <= plan2_cost {
        plan1_cost
    } else {
        plan2_cost
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires
        input.len() > 0,
        valid_input(input),
    ensures
        ({
            let parts = split_string_func(input);
            let n = string_to_int_func(parts[0]);
            let a = string_to_int_func(parts[1]);
            let b = string_to_int_func(parts[2]);
            result == int_to_string_func(min_parking_cost(n, a, b)) + seq!['\n']
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax for newline character literal */
    let parts = split_string_impl(&input);

    let n = string_to_int_impl(&parts[0]);
    let a = string_to_int_impl(&parts[1]);
    let b = string_to_int_impl(&parts[2]);

    let cost = min_parking_cost_impl(n, a, b);

    let mut result_vec = int_to_string_impl(cost);
    result_vec.push('\n');

    result_vec.into_seq()
}
// </vc-code>


}

fn main() {}