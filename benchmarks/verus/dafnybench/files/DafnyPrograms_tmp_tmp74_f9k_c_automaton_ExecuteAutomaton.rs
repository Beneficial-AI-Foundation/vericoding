use vstd::prelude::*;

verus! {

struct Automaton {}

#[verifier::exec_allows_no_decreases_clause]
fn execute_automaton(init: Seq<bool>, rule: spec_fn(bool, bool, bool) -> bool, steps: nat) 
    -> (table: Seq<Seq<bool>>)
    requires 

        init.len() >= 2
    ensures 

        table.len() == 1 + steps,

        table[0] == init,

        forall|i: int| 0 <= i < table.len() ==> #[trigger] table[i].len() == init.len()
{
    assume(false);
    unreached()
}

}
fn main() {}