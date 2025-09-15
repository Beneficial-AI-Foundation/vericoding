// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): witness to spec mapping */
spec fn square_exists_to_spec(n: nat, i: nat) -> bool { i * i == n ==> is_perfect_square(n) }
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate i up to m to find square witness with proper invariants */
    let m: nat = n as nat;
    let mut i: nat = 0;
    let mut found: bool = false;
    while (!found && i <= m)
        invariant { i <= m + 1 }
        invariant { forall|j: nat| j < i ==> j * j != m }
        decreases { m + 1 - i }
    {
        if i * i == m {
            found = true;
        } else {
            i = i + 1;
        }
    }
    proof {
        if found {
            assert(i * i == m);
            assert(exists|j: nat| j * j == m);
            assert(is_perfect_square(m));
        } else {
            assert(i > m);
            assert(forall|j: nat| j < i ==> j * j != m);
            assert(forall|j: nat| j <= m ==> j * j != m);
            assert(!exists|j: nat| j * j == m);
        }
    }
    found
}
// </vc-code>

}
fn main() {}