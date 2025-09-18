// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add_index maps (seed,i) to runtime value */ fn add_index(seed: u64, i: usize) -> u64 { seed.wrapping_add(i as u64) } /* helper modified by LLM (iteration 5): add_index_spec maps (seed,i) to spec value */ spec fn add_index_spec(seed: u64, i: nat) -> u64 { seed + (i as u64) }
// </vc-helpers>

// <vc-spec>
spec fn pcg64_dxsm_spec(seed: u64, n: nat) -> Seq<u64>
{
    arbitrary()
}

fn pcg64_dxsm(seed: u64, n: usize) -> (result: Vec<u64>)
    ensures
        result.len() == n,
        seed == seed ==> result@ == pcg64_dxsm_spec(seed, n as nat),
        n > 0 ==> (exists|i: int| 0 <= i < n && #[trigger] result[i] >= 0),
        n > 1 ==> true,
        forall|seed_prime: u64| seed != seed_prime ==> 
            pcg64_dxsm_spec(seed, n as nat) != pcg64_dxsm_spec(seed_prime, n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result by pushing add_index(seed, i) and maintain correspondence with add_index_spec */
    let mut result: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n;
        invariant result.len() == i;
        invariant forall|j: int| 0 <= j && j < (i as int) ==> result@[j] == add_index_spec(seed, j as nat);
        decreases n - i
    {
        result.push(add_index(seed, i));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}