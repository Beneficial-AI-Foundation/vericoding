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
// </vc-helpers>

// <vc-spec>
fn solve(s: u8, b: u8, attacking_powers: Vec<u8>, bases: Vec<(u8, u8)>) -> (result: Vec<u8>)
    requires valid_input(s as nat, b as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)))
    ensures valid_output(s as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)), result@.map(|i, x: u8| x as nat))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}