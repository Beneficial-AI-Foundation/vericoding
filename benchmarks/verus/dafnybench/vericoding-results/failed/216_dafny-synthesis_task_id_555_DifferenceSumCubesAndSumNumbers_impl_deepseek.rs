use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn sum_nat(n: nat) -> (sum: nat)
    ensures sum == n * (n + 1) / 2
    decreases n
{
    if n == 0 {
        0
    } else {
        let s = sum_nat(n - 1);
        (s + n) as nat
    }
}

proof fn sum_cubes(n: nat) -> (sum: nat)
    ensures sum == n * n * (n + 1) * (n + 1) / 4
    decreases n
{
    if n == 0 {
        0
    } else {
        let s = sum_cubes(n - 1);
        (s + (n as nat) * (n as nat) * (n as nat)) as nat
    }
}

proof lemma_sum_nat_formula(n: nat)
    ensures sum_nat(n) == n * (n + 1) / 2
    decreases n
{
    if n > 0 {
        lemma_sum_nat_formula((n - 1) as nat);
    }
}

proof lemma_sum_cubes_formula(n: nat)
    ensures sum_cubes(n) == n * n * (n + 1) * (n + 1) / 4
    decreases n
{
    if n > 0 {
        lemma_sum_cubes_formula((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_sum_cubes_formula(n as nat);
        lemma_sum_nat_formula(n as nat);
    }
    let sum_cubes_val = (n * n * (n + 1) * (n + 1)) / 4;
    let sum_nat_val = (n * (n + 1)) / 2;
    proof {
        assert(sum_cubes_val == sum_cubes(n as nat));
        assert(sum_nat_val == sum_nat(n as nat));
    }
    sum_cubes_val - sum_nat_val
}
// </vc-code>

fn main() {}

}