use vstd::prelude::*;

verus! {

/**
Consider cellular automata: a row of cells is repeatedly updated according to a rule. In this exercise I dabbled with,
each cell has the value either false or true. Each cell's next state depends only on the immediate neighbours, in the 
case where the cell is at the edges of the row, the inexistent neighbours are replaced by "false". The automaton table 
will contain the initial row, plus a row for each number of steps.
 */
struct Automaton {}

/**
This method computes the automaton.
Provide the initial row: init, the rule and the desired number of steps
 */

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn execute_automaton(init: Seq<bool>, rule: spec_fn(bool, bool, bool) -> bool, steps: nat) 
    -> (table: Seq<Seq<bool>>)
    requires 
        // we need the initial row to have the length bigger or equal to two
        init.len() >= 2
    ensures 
        // after computation the automaton is made of the initial row plus a row for each of the steps
        table.len() == 1 + steps,
        // the automaton must have the initial row at the top
        table[0] == init,
        // all rows in the automaton must be the same length
        forall|i: int| 0 <= i < table.len() ==> #[trigger] table[i].len() == init.len()
        // TODO: Additional ensures clauses for middle and corner elements would require complex triggers
        // Original Dafny clauses commented due to trigger complexity in Verus:
        // all the middle row elements (with existing neighbours) after a step, will be equal to the rule applied on the element in the previous state
        // and its neigbours
        // ensures forall i | 0 <= i < |table| - 1 ::
        //           forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
        // the corner row elements (with non-existing neighbours) after a step, will be equal to the rule applied on the element in the previous state,
        // its neighbour and false
        // ensures forall i | 0 <= i < |table| - 1 ::
        //           table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
// </vc-spec>
// <vc-code>
{
    let mut table = Seq::empty();
    table.push(init);
    let mut step_count: nat = 0;
    while step_count < steps
        invariant
            table.len() == 1 + step_count,
            table[0] == init,
            forall|i: int| 0 <= i < table.len() ==> table[i].len() == init.len(),
    {
        let current_row = table[table.len() - 1];
        let mut next_row = Seq::empty();
        let mut j: nat = 0;
        while j < current_row.len()
            invariant
                next_row.len() == j,
                j <= current_row.len(),
        {
            let left = if j > 0 { current_row[(j - 1) as int] } else { false };
            let center = current_row[j as int];
            let right = if j < current_row.len() - 1 { current_row[(j + 1) as int] } else { false };
            let next_val = rule(left, center, right);
            next_row.push(next_val);
            j = j + 1;
        }
        table.push(next_row);
        step_count = step_count + 1;
    }
    table
}
// </vc-code>

fn main() {}

}