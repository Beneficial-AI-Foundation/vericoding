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
/* helper modified by LLM (iteration 4): prove sum_gold_for_spaceship distributes over concatenation */
proof fn sum_concat(att: nat, a: Seq<(nat,nat)>, b: Seq<(nat,nat)>)
    ensures
        sum_gold_for_spaceship(att, a + b) == sum_gold_for_spaceship(att, a) + sum_gold_for_spaceship(att, b),
    decreases
        a.len()
{
    if a.len() == 0 {
        // base case: empty prefix, trivially holds
    } else {
        let head = a[0];
        let tail = a.subrange(1, a.len() as int);
        // recursive call without a proof block
        sum_concat(att, tail, b);
        assert(sum_gold_for_spaceship(att, tail + b) == sum_gold_for_spaceship(att, tail) + sum_gold_for_spaceship(att, b));
        if att >= head.0 {
            assert(sum_gold_for_spaceship(att, a + b) == head.1 + sum_gold_for_spaceship(att, tail + b));
            assert(sum_gold_for_spaceship(att, a) == head.1 + sum_gold_for_spaceship(att, tail));
            assert(sum_gold_for_spaceship(att, a + b) == sum_gold_for_spaceship(att, a) + sum_gold_for_spaceship(att, b));
        } else {
            assert(sum_gold_for_spaceship(att, a + b) == sum_gold_for_spaceship(att, tail + b));
            assert(sum_gold_for_spaceship(att, a) == sum_gold_for_spaceship(att, tail));
            assert(sum_gold_for_spaceship(att, a + b) == sum_gold_for_spaceship(att, a) + sum_gold_for_spaceship(att, b));
        }
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
    /* code modified by LLM (iteration 4): iterate spaces and sum gold per spaceship using integer accumulators */
    let s_usize = s as usize;
    let b_usize = b as usize;
    let mut result: Vec<u8> = Vec::new();
    result.reserve(s_usize);

    let mut i: usize = 0;
    while i < s_usize
        invariant
            i <= s_usize,
            result.len() == i,
        decreases
            s_usize - i
    {
        let att = attacking_powers[i] as u32;

        let mut j: usize = b_usize;
        let mut acc: u32 = 0;
        while j > 0
            invariant
                j <= b_usize,
                acc >= 0,
            decreases
                j
        {
            let idx = j - 1;
            let base = bases[idx];
            let base_attack = base.0 as u32;
            let base_gold = base.1 as u32;
            if att >= base_attack {
                acc = acc + base_gold;
            }
            j = idx;
        }

        result.push(acc as u8);
        i = i + 1;
    }

    result
}

// </vc-code>


}

fn main() {}