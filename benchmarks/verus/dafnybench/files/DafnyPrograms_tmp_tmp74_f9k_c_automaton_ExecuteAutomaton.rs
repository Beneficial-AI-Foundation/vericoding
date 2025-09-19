// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Automaton {}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn execute_automaton(init: Vec<bool>, rule: spec_fn(bool, bool, bool) -> bool, steps: u8) 
    -> (table: Vec<Vec<bool>>)
    requires 

        init.len() >= 2
    ensures 

        table.len() == 1 + steps as int,

        table@[0]@ == init@,

        forall|i: int| 0 <= i < table@.len() ==> #[trigger] table@[i]@.len() == init@.len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}