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
/* helper modified by LLM (iteration 5): fixed precondition requirements and added missing proof for invariant preservation */
proof fn lemma_sum_gold_append(attacking_power: nat, bases1: Seq<(nat, nat)>, bases2: Seq<(nat, nat)>)
    ensures sum_gold_for_spaceship(attacking_power, bases1 + bases2) == sum_gold_for_spaceship(attacking_power, bases1) + sum_gold_for_spaceship(attacking_power, bases2)
    decreases bases1.len()
{
    if bases1.len() == 0 {
        assert(bases1 + bases2 == bases2);
    } else {
        let rest1 = bases1.subrange(1, bases1.len() as int);
        let combined = bases1 + bases2;
        assert(combined[0] == bases1[0]);
        assert(combined.subrange(1, combined.len() as int) == rest1 + bases2);
        lemma_sum_gold_append(attacking_power, rest1, bases2);
    }
}

proof fn lemma_sum_gold_subrange_step(attacking_power: nat, bases: Seq<(nat, nat)>, i: int)
    requires 0 <= i < bases.len()
    ensures sum_gold_for_spaceship(attacking_power, bases.subrange(0, i + 1)) == 
        sum_gold_for_spaceship(attacking_power, bases.subrange(0, i)) + 
        (if attacking_power >= bases[i].0 then bases[i].1 else 0)
{
    let prefix = bases.subrange(0, i);
    let full_prefix = bases.subrange(0, i + 1);
    assert(full_prefix == prefix.push(bases[i]));
    
    if i == 0 {
        assert(prefix.len() == 0);
        assert(sum_gold_for_spaceship(attacking_power, prefix) == 0);
    } else {
        lemma_sum_gold_append(attacking_power, prefix, seq![bases[i]]);
    }
}

fn compute_gold_for_spaceship(attacking_power: u8, bases: &Vec<(u8, u8)>) -> (gold: u8)
    requires attacking_power <= 255,
        forall|i: int| 0 <= i < bases.len() ==> bases@[i].1 <= 100,
    ensures gold as nat == sum_gold_for_spaceship(attacking_power as nat, bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)))
{
    let mut total: u16 = 0;
    let mut i: usize = 0;
    
    while i < bases.len()
        invariant
            i <= bases.len(),
            total as nat == sum_gold_for_spaceship(attacking_power as nat, bases@.subrange(0, i as int).map(|j, x: (u8, u8)| (x.0 as nat, x.1 as nat))),
            total <= 25500,
        decreases bases.len() - i
    {
        let old_total = total;
        if attacking_power >= bases[i].0 {
            total = total + (bases[i].1 as u16);
        }
        
        proof {
            let mapped_bases = bases@.map(|j, x: (u8, u8)| (x.0 as nat, x.1 as nat));
            lemma_sum_gold_subrange_step(attacking_power as nat, mapped_bases, i as int);
            
            let added_value = if attacking_power >= bases[i].0 { bases[i].1 as nat } else { 0 };
            assert(total as nat == old_total as nat + added_value);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(bases@.subrange(0, bases.len() as int) == bases@);
    }
    
    if total > 255 {
        255
    } else {
        total as u8
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: u8, b: u8, attacking_powers: Vec<u8>, bases: Vec<(u8, u8)>) -> (result: Vec<u8>)
    requires valid_input(s as nat, b as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)))
    ensures valid_output(s as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)), result@.map(|i, x: u8| x as nat))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed precondition satisfaction and ensured proper bounds checking */
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    
    while i < s as usize && i < attacking_powers.len()
        invariant
            i <= s,
            i <= attacking_powers.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as nat == sum_gold_for_spaceship(attacking_powers@[j] as nat, bases@.map(|k, x: (u8, u8)| (x.0 as nat, x.1 as nat))),
        decreases s as usize - i
    {
        proof {
            assert(forall|k: int| 0 <= k < bases.len() ==> bases@[k].1 <= 100);
        }
        let gold = compute_gold_for_spaceship(attacking_powers[i], &bases);
        result.push(gold);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}