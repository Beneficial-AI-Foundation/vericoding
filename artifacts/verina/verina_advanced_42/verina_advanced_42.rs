use vstd::prelude::*;

verus! {

// Precondition (matches the original Lean - trivially true)
spec fn max_profit_precond(prices: Vec<u32>) -> bool {
    true
}

// Helper function to update minimum price and maximum profit
// Corresponds to updateMinAndProfit in Lean
fn update_min_and_profit(price: u32, min_so_far: u32, max_profit: u32) -> (u32, u32) {
    let new_min = if min_so_far <= price { min_so_far } else { price };
    let profit = if price > min_so_far { price - min_so_far } else { 0 };
    let new_max_profit = if max_profit >= profit { max_profit } else { profit };
    (new_min, new_max_profit)
}

// Auxiliary recursive function that corresponds to maxProfitAux in Lean
fn max_profit_aux(prices: &Vec<u32>, start_idx: usize, min_so_far: u32, max_profit: u32) -> (result: u32)
    requires start_idx <= prices.len()
    decreases prices.len() - start_idx
{
    if start_idx >= prices.len() {
        max_profit
    } else {
        let (new_min, new_profit) = update_min_and_profit(prices[start_idx], min_so_far, max_profit);
        max_profit_aux(prices, start_idx + 1, new_min, new_profit)
    }
}

// Main function that corresponds to maxProfit in Lean
fn max_profit(prices: Vec<u32>) -> (result: u32)
    requires max_profit_precond(prices)
{
    if prices.len() == 0 {
        0
    } else {
        max_profit_aux(&prices, 1, prices[0], 0)
    }
}

// Postcondition specification (corresponds to maxProfit_postcond in Lean)
spec fn max_profit_postcond(prices: Vec<u32>, result: u32) -> bool {
    (result == 0 && prices.len() == 0) ||
    (
        // All valid transactions have profit <= result
        (forall|i: int, j: int| 
            0 <= i < j < prices.len() ==> prices[j as int] - prices[i as int] <= result) &&
        
        // There exists a transaction with profit = result  
        (exists|i: int, j: int| 
            0 <= i < j < prices.len() && prices[j as int] - prices[i as int] == result)
    )
}

// Main theorem that corresponds to maxProfit_spec_satisfied in Lean
// Currently admits the proof like the original Lean code
fn max_profit_spec_satisfied(prices: Vec<u32>) -> (result: u32)
    requires max_profit_precond(prices)
    ensures max_profit_postcond(prices, result)
{
    let result = max_profit(prices);
    proof {
        // Original Lean proof was 'sorry' - using admit() for now
        admit();
    }
    result
}

fn main() {}

}