// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Automaton {}
// </vc-preamble>

// <vc-helpers>
fn compute_next_generation(current: &Vec<bool>, rule: spec_fn(bool, bool, bool) -> bool) -> (next: Vec<bool>)
    requires
        current.len() >= 2,
    ensures
        next.len() == current.len(),
        forall|i: int| 0 <= i < next.len() ==> #[trigger] next@[i] == rule(
            current@[if i == 0 { current.len() - 1 } else { i - 1 }],
            current@[i],
            current@[if i == current.len() - 1 { 0 } else { i + 1 }],
        ),
{
    let len = current.len();
    Vec::from_fn(len, |i: usize| {
        let left = if i == 0 { current[len - 1] } else { current[i - 1] };
        let center = current[i];
        let right = if i == len - 1 { current[0] } else { current[i + 1] };
        rule(left, center, right)
    })
}
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
    let mut table: Vec<Vec<bool>> = Vec::new();
    table.push(init.to_vec());
    let mut i: nat = 0;
    while i < steps
        invariant
            0 <= i <= steps,
            table@.len() == i + 1,
            table@[0] == init,
            forall|j: int| 0 <= j < table@.len() ==> #[trigger] table@[j].len() == init.len(),
        decreases steps - i
    {
        let prev_gen = &table[i as usize];
        let next_gen = compute_next_generation(prev_gen, rule);
        table.push(next_gen);
        i = i + 1;
    }
    table
}
// </vc-code>

}
fn main() {}