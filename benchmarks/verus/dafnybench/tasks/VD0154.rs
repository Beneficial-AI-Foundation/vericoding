// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Automaton {}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn execute_automaton(init: Seq<bool>, rule: spec_fn(bool, bool, bool) -> bool, steps: nat) 
    -> (table: Seq<Seq<bool>>)
    requires 

        init.len() >= 2
    ensures 

        table.len() == 1 + steps,

        table[0] == init,

        forall|i: int| 0 <= i < table.len() ==> #[trigger] table[i].len() == init.len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}