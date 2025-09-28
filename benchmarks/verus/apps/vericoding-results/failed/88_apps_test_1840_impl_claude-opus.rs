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
proof fn lemma_sum_gold_subrange(attacking_power: nat, bases: Seq<(nat, nat)>, i: int)
    requires
        0 <= i < bases.len(),
    ensures
        sum_gold_for_spaceship(attacking_power, bases.subrange(i, bases.len() as int)) ==
        if attacking_power >= bases[i].0 {
            bases[i].1 + sum_gold_for_spaceship(attacking_power, bases.subrange(i + 1, bases.len() as int))
        } else {
            sum_gold_for_spaceship(attacking_power, bases.subrange(i + 1, bases.len() as int))
        }
{
    assert(bases.subrange(i, bases.len() as int).len() > 0);
    assert(bases.subrange(i, bases.len() as int)[0] == bases[i]);
    assert(bases.subrange(i, bases.len() as int).subrange(1, bases.subrange(i, bases.len() as int).len() as int) ==
           bases.subrange(i + 1, bases.len() as int));
}
// </vc-helpers>

// <vc-spec>
fn solve(s: u8, b: u8, attacking_powers: Vec<u8>, bases: Vec<(u8, u8)>) -> (result: Vec<u8>)
    requires valid_input(s as nat, b as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)))
    ensures valid_output(s as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)), result@.map(|i, x: u8| x as nat))
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut spaceship_idx: usize = 0;
    
    while spaceship_idx < s as usize
        invariant
            spaceship_idx <= s as usize,
            result.len() == spaceship_idx,
            forall|j: int| 0 <= j < spaceship_idx ==> result@[j] as nat == sum_gold_for_spaceship(attacking_powers@[j] as nat, bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat))),
    {
        let attacking_power = attacking_powers[spaceship_idx];
        let mut gold_sum: u8 = 0;
        let mut base_idx: usize = 0;
        
        while base_idx < b as usize
            invariant
                base_idx <= b as usize,
                gold_sum as nat == sum_gold_for_spaceship(attacking_power as nat, bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)).subrange(0, base_idx as int)),
        {
            proof {
                lemma_sum_gold_subrange(attacking_power as nat, bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)), base_idx as int);
            }
            
            if attacking_power >= bases[base_idx].0 {
                gold_sum = gold_sum + bases[base_idx].1;
            }
            base_idx = base_idx + 1;
        }
        
        assert(bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)).subrange(0, b as int) == bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)));
        result.push(gold_sum);
        spaceship_idx = spaceship_idx + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}