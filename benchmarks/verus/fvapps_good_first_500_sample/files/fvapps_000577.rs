// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn sum_list(prices: Seq<nat>) -> nat 
    decreases prices.len()
{
    if prices.len() == 0 {
        0
    } else {
        prices[0] + sum_list(prices.skip(1))
    }
}

fn get_pangram_cost(prices: Vec<nat>, text: Vec<u8>) -> (result: nat)
    requires prices.len() == 26,
    ensures 
        result >= 0,
        text.len() == 0 ==> result == sum_list(prices@)
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
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // Test cases would go here but are commented out for verification
    // let prices1 = vec![1nat, 2nat, 3nat, 4nat, 5nat, 6nat, 7nat, 8nat, 9nat, 10nat, 11nat, 12nat, 13nat, 14nat, 15nat, 16nat, 17nat, 18nat, 19nat, 20nat, 21nat, 22nat, 23nat, 24nat, 25nat, 26nat];
    // let result1 = get_pangram_cost(prices1, "abcdefghijklmopqrstuvwz".as_bytes().to_vec());
    // println!("{}", result1); // Expected: 63
    
    // let prices2 = vec![1nat, 2nat, 3nat, 4nat, 5nat, 6nat, 7nat, 8nat, 9nat, 10nat, 11nat, 12nat, 13nat, 14nat, 15nat, 16nat, 17nat, 18nat, 19nat, 20nat, 21nat, 22nat, 23nat, 24nat, 25nat, 26nat];
    // let result2 = get_pangram_cost(prices2, "thequickbrownfoxjumpsoverthelazydog".as_bytes().to_vec());
    // println!("{}", result2); // Expected: 0
    
    // let prices3 = vec![1nat; 26];
    // let result3 = get_pangram_cost(prices3, "a".as_bytes().to_vec());
    // println!("{}", result3); // Expected: 25
}