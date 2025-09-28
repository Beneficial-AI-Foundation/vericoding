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
fn apply_rule_to_row(row: Seq<bool>, rule: spec_fn(bool, bool, bool) -> bool) -> (result: Seq<bool>)
    requires row.len() >= 2
    ensures result.len() == row.len()
{
    let mut new_row = Vec::new();
    
    // First element (left edge)
    new_row.push(rule(false, row@[0], row@[1]));
    
    // Middle elements
    let mut i: usize = 1;
    while i < (row.len() - 1) as usize
        invariant 
            1 <= i <= (row.len() - 1) as usize,
            new_row.len() == i,
            row.len() >= 2
    {
        new_row.push(rule(row@[i - 1], row@[i], row@[i + 1]));
        i += 1;
    }
    
    // Last element (right edge)
    new_row.push(rule(row@[row.len() - 2], row@[row.len() - 1], false));
    
    new_row@
}
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
    let mut table = Vec::new();
    table.push(init);
    
    let mut step: usize = 0;
    while step < steps as usize
        invariant 
            table.len() == step + 1,
            step <= steps as usize,
            table@[0] == init,
            forall|i: int| 0 <= i < table.len() ==> #[trigger] table@[i].len() == init.len()
    {
        let current_row = table@[step];
        let next_row = apply_rule_to_row(current_row, rule);
        table.push(next_row);
        step += 1;
    }
    
    table@
}
// </vc-code>

fn main() {}

}