// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: nat, b: nat, attacking_powers: Seq<nat>, bases: Seq<(nat, nat)>) -> bool {
    attacking_powers.len() == s && bases.len() == b
}

spec fn sum_gold_for_spaceship(attacking_power: nat, bases: Seq<(nat, nat)>) -> nat
    decreases bases.len()
{
    if bases.len() == 0 {
        0
    } else if attacking_power >= bases[0].0 {
        bases[0].1 + sum_gold_for_spaceship(attacking_power, bases.subrange(1, bases.len() as int))
    } else {
        sum_gold_for_spaceship(attacking_power, bases.subrange(1, bases.len() as int))
    }
}

spec fn valid_output(s: nat, attacking_powers: Seq<nat>, bases: Seq<(nat, nat)>, result: Seq<nat>) -> bool {
    result.len() == s &&
    (forall|i: int| 0 <= i < s ==> result[i] >= 0) &&
    (forall|i: int| 0 <= i < s && i < attacking_powers.len() ==> 
        result[i] == sum_gold_for_spaceship(attacking_powers[i], bases))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix lemma_sum_gold_recursive calls with proper arguments */

spec fn valid_base_for_power(attacking_power: nat, base: (nat, nat)) -> bool {
    attacking_power >= base.0
}

proof fn lemma_sum_gold_recursive(attacking_power: nat, bases: Seq<(nat, nat)>, result: nat)
    requires bases.len() > 0,
    ensures sum_gold_for_spaceship(attacking_power, bases) == (
        if valid_base_for_power(attacking_power, bases[0]) {
            bases[0].1 + sum_gold_for_spaceship(attacking_power, bases.subrange(1, bases.len() as int))
        } else {
            sum_gold_for_spaceship(attacking_power, bases.subrange(1, bases.len() as int))
        }
    )
{
}

proof fn lemma_sum_gold_empty(attacking_power: nat)
    ensures sum_gold_for_spaceship(attacking_power, Seq::empty()) == 0
{
}

fn compute_gold_for_ship(attacking_power: u8, bases: &Vec<(u8, u8)>) -> (gold: u8)
    requires
        bases@.len() as nat == (bases.len() as nat),
    ensures
        gold as nat == sum_gold_for_spaceship(
            attacking_power as nat, 
            bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat))
        )
{
    let mut total_gold: u8 = 0;
    let mut i: usize = 0;
    
    while i < bases.len()
        invariant
            i <= bases.len(),
            total_gold as nat == sum_gold_for_spaceship(
                attacking_power as nat, 
                bases@.subrange(0, i as int).map(|j, x: (u8, u8)| (x.0 as nat, x.1 as nat))
            ),
            total_gold <= 255u8,
        decreases bases.len() - i
    {
        let (min_defense, gold_reward) = bases[i];
        
        if attacking_power >= min_defense {
            proof {
                lemma_sum_gold_recursive(attacking_power as nat, 
                    bases@.subrange(0, i as int + 1).map(|j, x: (u8, u8)| (x.0 as nat, x.1 as nat)),
                    sum_gold_for_spaceship(attacking_power as nat, bases@.subrange(0, i as int + 1).map(|j, x: (u8, u8)| (x.0 as nat, x.1 as nat))));
            }
            assert(total_gold + gold_reward <= 255u8) by {
                assert(total_gold as nat + gold_reward as nat <= 255u8 as nat);
            };
            total_gold = total_gold + gold_reward;
        } else {
            proof {
                lemma_sum_gold_recursive(attacking_power as nat, 
                    bases@.subrange(0, i as int + 1).map(|j, x: (u8, u8)| (x.0 as nat, x.1 as nat)),
                    sum_gold_for_spaceship(attacking_power as nat, bases@.subrange(0, i as int + 1).map(|j, x: (u8, u8)| (x.0 as nat, x.1 as nat))));
            }
        }
        
        i = i + 1;
    }
    
    total_gold
}
// </vc-helpers>

// <vc-spec>
fn solve(s: u8, b: u8, attacking_powers: Vec<u8>, bases: Vec<(u8, u8)>) -> (result: Vec<u8>)
    requires valid_input(s as nat, b as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)))
    ensures valid_output(s as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)), result@.map(|i, x: u8| x as nat))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): maintain original implementation */
{
    let mut result: Vec<u8> = Vec::new();
    let mut ship_index: usize = 0;
    
    while ship_index < s as usize
        invariant
            0 <= ship_index <= s as usize,
            ship_index <= attacking_powers.len(),
            result.len() == ship_index,
            forall|j: int| 0 <= j < ship_index ==> 
                result[j] as nat == sum_gold_for_spaceship(
                    attacking_powers[j] as nat,
                    bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat))
                )
        decreases (s as usize) - ship_index
    {
        if ship_index < attacking_powers.len() {
            let gold = compute_gold_for_ship(attacking_powers[ship_index], &bases);
            result.push(gold);
        } else {
            result.push(0u8);
        }
        ship_index = ship_index + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}