// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_prices(voters: Seq<(usize, usize)>) -> nat 
    decreases voters.len()
{
    if voters.len() == 0 {
        0nat
    } else {
        voters[0].1 as nat + sum_prices(voters.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve_elections(n: usize, voters: Vec<(usize, usize)>) -> (result: usize)
    requires 
        n > 0,
        voters.len() == n,
        forall|i: int| 0 <= i < voters.len() ==> voters[i].0 < n,
    ensures
        result >= 0,
        result <= sum_prices(voters@),
        (forall|i: int| 0 <= i < voters.len() ==> voters[i].0 == 0) ==> result == 0,
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
    // let test1 = solve_elections(3, vec![(1, 5), (2, 10), (2, 8)]);
    // println!("{}", test1); // Expected: 8

    // let test2 = solve_elections(7, vec![(0, 1), (3, 1), (1, 1), (6, 1), (1, 1), (4, 1), (4, 1)]);
    // println!("{}", test2); // Expected: 0

    // let test3 = solve_elections(6, vec![(2, 6), (2, 3), (2, 8), (2, 7), (4, 4), (5, 5)]);
    // println!("{}", test3); // Expected: 7
}