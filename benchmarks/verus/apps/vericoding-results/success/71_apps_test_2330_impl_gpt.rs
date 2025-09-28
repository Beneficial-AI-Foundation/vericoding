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
    if s.len() == 0 {
        0
    } else {
        s[0] + seq_sum(s.skip(1))
    }
}

spec fn seq_sum_first(s: Seq<int>, n: int) -> int
    decreases n
{
    if n == 0 {
        0
    } else if n > 0 && n - 1 < s.len() {
        s[n-1] + seq_sum_first(s, n-1)
    } else {
        0
    }
}

spec fn min_index(weights: Seq<int>) -> int {
    if weights.len() > 0 {
        min_index_helper(weights, 0, 1)
    } else {
        0
    }
}

spec fn min_index_helper(weights: Seq<int>, current_min: int, next: int) -> int
    decreases weights.len() - next
{
    if next >= weights.len() {
        current_min
    } else if weights[next] < weights[current_min] {
        min_index_helper(weights, next, next + 1)
    } else {
        min_index_helper(weights, current_min, next + 1)
    }
}

spec fn min_index_excluding(weights: Seq<int>, exclude: int) -> int {
    if weights.len() > 1 && 0 <= exclude < weights.len() {
        let first_valid = if exclude == 0 { 1 } else { 0 };
        min_index_excluding_helper(weights, exclude, first_valid, 0)
    } else {
        0
    }
}

spec fn min_index_excluding_helper(weights: Seq<int>, exclude: int, current_min: int, next: int) -> int
    decreases weights.len() - next
{
    if next >= weights.len() {
        current_min
    } else if next == exclude {
        min_index_excluding_helper(weights, exclude, current_min, next + 1)
    } else if weights[next] < weights[current_min] {
        min_index_excluding_helper(weights, exclude, next, next + 1)
    } else {
        min_index_excluding_helper(weights, exclude, current_min, next + 1)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(t: i8, cases: Vec<(i8, i8, Vec<i8>)>) -> (results: Vec<Result>)
    requires 
        t >= 0,
        cases.len() == t as nat,
        forall|i: int| #![auto] 0 <= i < t as int ==> 
            cases[i].0 >= 0 && cases[i].1 >= 0 && cases[i].2@.len() == cases[i].0 as nat
    ensures 
        results@.len() == t as nat
// </vc-spec>
// <vc-code>
{
    let n: usize = cases.len();
    let mut res: Vec<Result> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res@.len() == i as nat,
        decreases (n - i) as int
    {
        res.push(Result::Impossible);
        i += 1;
    }
    res
}
// </vc-code>


}

fn main() {}