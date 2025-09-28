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
/* helper modified by LLM (iteration 3): define first-k spec without requires; guarded on empty bases and k == 0 */
spec fn sum_gold_first_k(attacking_power: nat, bases: Seq<(nat, nat)>, k: nat) -> nat
    decreases k
{
    if k == 0 || bases.len() == 0 {
        0
    } else {
        let h = bases[0];
        let rest = bases.subrange(1, bases.len() as int);
        (if attacking_power >= h.0 { h.1 } else { 0 }) + sum_gold_first_k(attacking_power, rest, (k - 1) as nat)
    }
}

/* helper modified by LLM (iteration 3): lemma connecting first-k with full sum, by induction on bases */
proof fn lemma_first_k_full(attacking_power: nat, bases: Seq<(nat, nat)>)
    ensures
        sum_gold_first_k(attacking_power, bases, bases.len()) == sum_gold_for_spaceship(attacking_power, bases),
    decreases bases.len()
{
    if bases.len() == 0 {
        assert(sum_gold_first_k(attacking_power, bases, bases.len()) == 0);
        assert(sum_gold_for_spaceship(attacking_power, bases) == 0);
    } else {
        let h = bases[0];
        let rest = bases.subrange(1, bases.len() as int);
        lemma_first_k_full(attacking_power, rest);
        proof {
            assert(rest.len() == bases.len() - 1);
            let k = bases.len();
            assert(k > 0);
            assert(((k - 1) as nat) == rest.len());
            assert(sum_gold_first_k(attacking_power, bases, k)
                == (if attacking_power >= h.0 { h.1 } else { 0 }) + sum_gold_first_k(attacking_power, rest, ((k - 1) as nat)));
            assert(sum_gold_for_spaceship(attacking_power, bases)
                == (if attacking_power >= h.0 { h.1 } else { 0 }) + sum_gold_for_spaceship(attacking_power, rest));
            assert(sum_gold_first_k(attacking_power, rest, rest.len()) == sum_gold_for_spaceship(attacking_power, rest));
        }
        assert(sum_gold_first_k(attacking_power, bases, bases.len())
            == (if attacking_power >= h.0 { h.1 } else { 0 }) + sum_gold_for_spaceship(attacking_power, rest));
        assert(sum_gold_for_spaceship(attacking_power, bases)
            == (if attacking_power >= h.0 { h.1 } else { 0 }) + sum_gold_for_spaceship(attacking_power, rest));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: u8, b: u8, attacking_powers: Vec<u8>, bases: Vec<(u8, u8)>) -> (result: Vec<u8>)
    requires valid_input(s as nat, b as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)))
    ensures valid_output(s as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)), result@.map(|i, x: u8| x as nat))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): iterative computation of sums per spaceship over bases */
{
    let s_len = attacking_powers.len();
    let mut res: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s_len
        invariant
            i <= s_len,
            res.len() == i,
        decreases s_len - i
    {
        let ap: u8 = attacking_powers[i];
        let mut j: usize = 0;
        let b_len = bases.len();
        let mut sum: u32 = 0;
        while j < b_len
            invariant
                j <= b_len,
            decreases b_len - j
        {
            let base = bases[j];
            if ap >= base.0 {
                sum = sum + (base.1 as u32);
            }
            j = j + 1;
        }
        let sum_u8: u8 = sum as u8;
        res.push(sum_u8);
        i = i + 1;
    }
    res
}
// </vc-code>


}

fn main() {}