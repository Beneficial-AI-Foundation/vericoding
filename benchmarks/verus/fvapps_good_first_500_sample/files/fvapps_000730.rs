// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn total_cost_lists(costs: Seq<Seq<usize>>) -> nat
    decreases costs.len()
{
    if costs.len() == 0 {
        0
    } else {
        row_sum(costs[0]) + total_cost_lists(costs.skip(1))
    }
}

spec fn row_sum(row: Seq<usize>) -> nat
    decreases row.len()
{
    if row.len() == 0 {
        0
    } else {
        (row[0] as nat) + row_sum(row.skip(1))
    }
}

spec fn max_element_lists(costs: Seq<Seq<usize>>) -> usize
    decreases costs.len()
{
    if costs.len() == 0 {
        0
    } else {
        spec_max(row_max(costs[0]), max_element_lists(costs.skip(1)))
    }
}

spec fn row_max(row: Seq<usize>) -> usize
    decreases row.len()
{
    if row.len() == 0 {
        0
    } else {
        spec_max(row[0], row_max(row.skip(1)))
    }
}

spec fn spec_max(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}

fn min_cable_cost(n: usize, costs: Vec<Vec<usize>>) -> (result: usize)
    requires 
        n > 0,
        costs.len() == n,
        forall|i: int| 0 <= i < n ==> costs[i].len() == n,
    ensures 
        result <= total_cost_lists(costs@.map(|i: int, row: Vec<usize>| row@)) / 2,
        result <= (n * (n - 1)) / 2 * (max_element_lists(costs@.map(|i: int, row: Vec<usize>| row@)) as nat),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let result = min_cable_cost(4, vec![vec![0, 7, 8, 10], vec![7, 0, 4, 5], vec![8, 4, 0, 6], vec![10, 5, 6, 0]]);
    // println!("{}", result);
    
    // let result2 = min_cable_cost(3, vec![vec![0, 1, 2], vec![1, 0, 3], vec![2, 3, 0]]);
    // println!("{}", result2);
}