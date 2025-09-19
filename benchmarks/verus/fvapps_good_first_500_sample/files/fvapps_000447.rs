// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn list_min(coins: Seq<u32>) -> u32
    decreases coins.len()
{
    if coins.len() == 0 {
        0
    } else if coins.len() == 1 {
        coins[0]
    } else {
        let x = coins[0];
        let min_rest = list_min(coins.skip(1));
        if x < min_rest { x } else { min_rest }
    }
}
// </vc-helpers>

// <vc-spec>
fn coin_change(coins: Vec<u32>, amount: u32) -> (result: i32)
    requires 
        coins.len() > 0,
        forall|i: int| 0 <= i < coins.len() ==> coins[i] > 0 && coins[i] <= 20,
    ensures 
        result >= -1,
        result != -1 ==> result <= amount,
        amount == 0 ==> result == 0,
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
    // let result1 = coin_change(vec![1, 2, 5], 11);
    // println!("{}", result1); // Should print 3

    // let result2 = coin_change(vec![2], 3);
    // println!("{}", result2); // Should print -1

    // let result3 = coin_change(vec![1], 0);
    // println!("{}", result3); // Should print 0
}