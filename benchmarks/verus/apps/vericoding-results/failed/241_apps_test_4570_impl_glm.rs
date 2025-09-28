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
/* helper modified by LLM (iteration 5): Change to use Vec<char> instead of Seq<char> */
fn split_string_exec(s: Vec<char>) -> (parts: Vec<Vec<char>>)
    ensures
        parts@ == split_string_func(s@),
{
    vec![vec!['1'], vec!['2'], vec!['3']]
}

/* helper modified by LLM (iteration 5): Change to use Vec<char> and avoid @ indexing */
fn string_to_int_exec(s: Vec<char>) -> (n: i32)
    ensures
        n as int == string_to_int_func(s@),
{
    if s.len() > 0 && s[0] == '1' { 1 }
    else if s.len() > 0 && s[0] == '2' { 2 }
    else if s.len() > 0 && s[0] == '3' { 3 }
    else { 0 }
}

/* helper modified by LLM (iteration 5): Change to return Vec<char> */
fn int_to_string_exec(n: i32) -> (s: Vec<char>)
    ensures
        s@ == int_to_string_func(n as int),
{
    if n == 0 { vec!['0'] }
    else if n == 1 { vec!['1'] }
    else if n == 2 { vec!['2'] }
    else if n == 3 { vec!['3'] }
    else { vec!['0'] }
}

/* helper modified by LLM (iteration 5): No change needed */
fn min_parking_cost_exec(n: i32, a: i32, b: i32) -> (cost: i32)
    ensures
        cost as int == min_parking_cost(n as int, a as int, b as int),
{
    let plan1_cost = n * a;
    let plan2_cost = b;
    if plan1_cost <= plan2_cost { plan1_cost } else { plan2_cost }
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
/* code modified by LLM (iteration 5): Convert input to Vec and use new helpers */
{
    let input_vec = vstd::seq_lib::seq_to_vec(input);
    let parts = split_string_exec(input_vec);
    let n = string_to_int_exec(parts[0]);
    let a = string_to_int_exec(parts[1]);
    let b = string_to_int_exec(parts[2]);
    let cost = min_parking_cost_exec(n, a, b);
    let mut result_str = int_to_string_exec(cost);
    result_str.push('\n');
    result_str@
}
// </vc-code>


}

fn main() {}