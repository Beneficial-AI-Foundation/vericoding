// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn unique_paths_spec(m: nat, n: nat) -> nat
    recommends m > 0 && n > 0
    decreases m + n
{
    if m == 1 || n == 1 {
        1nat
    } else if m > 1 && n > 1 {
        unique_paths_spec(sub(m, 1nat), n) + unique_paths_spec(m, sub(n, 1nat))
    } else {
        0nat
    }
}

fn unique_paths(m: u32, n: u32) -> (result: u32)
    requires m > 0 && n > 0,
    ensures 
        result > 0,
        result == unique_paths_spec(m as nat, n as nat) as u32
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

proof fn unique_paths_positive(m: u32, n: u32)
    requires m > 0 && n > 0,
    ensures unique_paths_spec(m as nat, n as nat) > 0,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn unique_paths_symmetry(m: u32, n: u32)
    ensures unique_paths_spec(m as nat, n as nat) == unique_paths_spec(n as nat, m as nat),
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn unique_paths_single_row(n: u32)
    requires n > 0,
    ensures unique_paths_spec(1nat, n as nat) == 1nat,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn unique_paths_single_col(n: u32)
    requires n > 0,
    ensures unique_paths_spec(n as nat, 1nat) == 1nat,
{
    assume(false); // TODO: Remove this line and implement the proof
}

}

fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible
    
    // assert(unique_paths(3, 2) == 3);
    // assert(unique_paths(7, 3) == 28);
    // assert(unique_paths(3, 7) == 28);
}