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
/* helper modified by LLM (iteration 5): fixed slicing by borrowing the subslice */
fn exec_sum_gold(sp: u8, bs: &[(u8, u8)]) -> (res: u8)
    ensures
        res as nat == sum_gold_for_spaceship(sp as nat, bs@.map(|i: int, x: (u8, u8)| (x.0 as nat, x.1 as nat))),   decreases bs@.len()
{
    if bs.len() == 0 {
        0
    } else if sp >= bs[0].0 {
        let tail_sum = exec_sum_gold(sp, &bs[1..]);
        bs[0].1 + tail_sum
    } else {
        exec_sum_gold(sp, &bs[1..])
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: u8, b: u8, attacking_powers: Vec<u8>, bases: Vec<(u8, u8)>) -> (result: Vec<u8>)
    requires valid_input(s as nat, b as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)))
    ensures valid_output(s as nat, attacking_powers@.map(|i, x: u8| x as nat), bases@.map(|i, x: (u8, u8)| (x.0 as nat, x.1 as nat)), result@.map(|i, x: u8| x as nat))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes */
{
    let ghost apseq = attacking_powers@.map(|i: int, x: u8| x as nat);
    let ghost bseq = bases@.map(|i: int, x: (u8, u8)| (x.0 as nat, x.1 as nat));
    proof {
        assert(valid_input(s as nat, b as nat, apseq, bseq));
    }
    let mut result: Vec<u8> = Vec::with_capacity(s as usize);
    let mut z = 0usize;
    while z < (s as usize)
        invariant
            z == result.len(),
            z <= s as usize,
            forall|i: int| 0 <= i < z ==> result@[i] as nat == sum_gold_for_spaceship(apseq[i], bseq),
        decreases s as usize - z
    {
        let ap = attacking_powers[z];
        let sum = exec_sum_gold(ap, &bases);
        result.push(sum);
        z = z + 1;
        proof {
            assert(forall|i: int| 0 <= i < z ==> result@[i] as nat == sum_gold_for_spaceship(apseq[i], bseq));
        }
    }
    proof {
        assert(forall|i: int| 0 <= i < s ==> result@[i] as nat == sum_gold_for_spaceship(apseq[i], bseq));
    }
    result
}
// </vc-code>


}

fn main() {}