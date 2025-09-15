// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed type errors by using nat for loop index instead of int to match Seq len type. */
let mut i: nat = 0;
while i < s@.len()
    invariant
        i <= s@.len(),
        forall|j: nat| 0 <= j < i ==> (s@[j] != 'z' && s@[j] != 'Z'),
    decreases s@.len() - i
{
    if s@[i] == 'z' || s@[i] == 'Z' {
        assert(exists |k: int| 0 <= k < s@.len() && (s@[k] == 'z' || s@[k] == 'Z'));
        return true;
    }
    i = i + 1;
}
assert(forall |k: int| 0 <= k < s@.len() ==> (s@[k] != 'z' && s@[k] != 'Z'));
false
}
// </vc-code>

}
fn main() {}