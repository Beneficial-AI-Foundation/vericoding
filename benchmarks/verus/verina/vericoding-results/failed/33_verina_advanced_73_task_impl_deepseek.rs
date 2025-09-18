// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert binary_search to use ghost parameters and fix int/nat usage */
spec fn binary_search(l: Seq<nat>, target: nat, low: int, high: int) -> (result: bool)
    requires
        0 <= low <= high + 1,
        high < l.len(),
        forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j]
    ensures result == l.contains(target)
{
    if low > high {
        false
    } else {
        let mid = low + (high - low) / 2;
        if l[mid] == target {
            true
        } else if l[mid] < target {
            binary_search(l, target, mid + 1, high)
        } else {
            binary_search(l, target, low, mid - 1)
        }
    }
}

proof fn binary_search_proof(l: Seq<nat>, target: nat, low: int, high: int)
    requires
        0 <= low <= high + 1,
        high < l.len(),
        forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j]
    ensures binary_search(l, target, low, high) == l.contains(target)
{
    if low > high {
        assert(!l.contains(target));
    } else {
        let mid = low + (high - low) / 2;
        if l[mid] == target {
            assert(l.contains(target));
        } else if l[mid] < target {
            binary_search_proof(l, target, mid + 1, high);
        } else {
            binary_search_proof(l, target, low, mid - 1);
        }
    }
}

fn smallest_helper(l: Seq<nat>, candidate: nat) -> (result: bool)
    ensures result == l.contains(candidate)
{
    if l.len() == 0 {
        false
    } else {
        proof {
            binary_search_proof(l, candidate, 0, (l.len() - 1) as int);
        }
        binary_search(l, candidate, 0, (l.len() - 1) as int)
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_missing(l: Seq<nat>) -> (result: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Remove ghost usage and fix int/nat casting */
{
    let mut candidate: nat = 0;
    let len_nat = l.len();
    
    while candidate < len_nat
        invariant
            candidate >= 0,
            forall|i: nat| i < candidate ==> l.contains(i)
    {
        if !smallest_helper(l, candidate) {
            return candidate;
        }
        candidate = candidate + 1;
    }
    
    len_nat
}
// </vc-code>

}
fn main() {}