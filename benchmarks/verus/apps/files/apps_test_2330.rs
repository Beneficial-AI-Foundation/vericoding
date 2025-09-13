// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum Result {
    Impossible,
    Possible { cost: int, edges: Seq<(int, int)> }
}

spec fn seq_sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + seq_sum(s.subrange(1, s.len() as int)) }
}

spec fn seq_sum_first(s: Seq<int>, n: int) -> int
    requires 0 <= n <= s.len()
    decreases n
{
    if n == 0 { 0 } else { s[n-1] + seq_sum_first(s, n-1) }
}

spec fn min_index(weights: Seq<int>) -> int
    requires weights.len() > 0
{
    min_index_helper(weights, 0, 1)
}

spec fn min_index_helper(weights: Seq<int>, current_min: int, next: int) -> int
    requires 
        weights.len() > 0,
        0 <= current_min < weights.len(),
        0 <= next <= weights.len(),
    decreases weights.len() - next
{
    if next >= weights.len() { current_min }
    else if weights[next] < weights[current_min] { min_index_helper(weights, next, next + 1) }
    else { min_index_helper(weights, current_min, next + 1) }
}

spec fn min_index_excluding(weights: Seq<int>, exclude: int) -> int
    requires 
        weights.len() > 1,
        0 <= exclude < weights.len(),
{
    let first_valid = if exclude == 0 { 1 } else { 0 };
    min_index_excluding_helper(weights, exclude, first_valid, 0)
}

spec fn min_index_excluding_helper(weights: Seq<int>, exclude: int, current_min: int, next: int) -> int
    requires 
        weights.len() > 1,
        0 <= exclude < weights.len(),
        0 <= current_min < weights.len(),
        current_min != exclude,
        0 <= next <= weights.len(),
    decreases weights.len() - next
{
    if next >= weights.len() { current_min }
    else if next == exclude { min_index_excluding_helper(weights, exclude, current_min, next + 1) }
    else if weights[next] < weights[current_min] { min_index_excluding_helper(weights, exclude, next, next + 1) }
    else { min_index_excluding_helper(weights, exclude, current_min, next + 1) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(t: int, cases: Seq<(int, int, Seq<int>)>) -> (results: Seq<Result>)
    requires 
        t >= 0,
        cases.len() == t,
        forall|i: int| 0 <= i < t ==> 
            cases[i].0 >= 0 && cases[i].1 >= 0 && cases[i].2.len() == cases[i].0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    seq![]
    // impl-end
}
// </vc-code>


}

fn main() {}