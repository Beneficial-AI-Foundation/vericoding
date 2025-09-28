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
fn compute_next_row(
    current_row: Seq<bool>,
    rule: spec_fn(bool, bool, bool) -> bool,
    row_len: nat,
) -> (next_row_out: Seq<bool>) {
    requires(row_len == current_row.len());
    ensures(next_row_out.len() == row_len);
    ensures(forall|j: int| 0 <= j < row_len ==>
        #[trigger] next_row_out[j] == {
            if j == 0 {
                rule(false, current_row[0], current_row[1])
            } else if j == row_len - 1 {
                rule(current_row[row_len - 2], current_row[row_len - 1], false)
            } else {
                rule(current_row[j - 1], current_row[j], current_row[j + 1])
            }
        }
    );

    let mut next_row_cells: Vec<bool> = Vec::new();
    next_row_cells.reserve(row_len as usize);

    proof {
        next_row_cells.set_len(row_len as usize);
    }

    let mut j: int = 0;
    while j < row_len
        invariant 
            0 <= j <= row_len,
            next_row_cells.len() == row_len as usize,
            forall|k: int| 0 <= k < j ==> #[trigger] next_row_cells.view_as_seq()[k] == {
                if k == 0 {
                    rule(false, current_row[0], current_row[1])
                } else if k == row_len - 1 {
                    rule(current_row[row_len - 2], current_row[row_len - 1], false)
                } else {
                    rule(current_row[k - 1], current_row[k], current_row[k + 1])
                }
            }
    {
        let cell_value = if j == 0 {
            rule(false, current_row[0], current_row[1])
        } else if j == row_len - 1 {
            rule(current_row[row_len - 2], current_row[row_len - 1], false)
        } else {
            rule(current_row[j - 1], current_row[j], current_row[j + 1])
        };
        next_row_cells.set(j as usize, cell_value);
        j = j + 1;
    }
    next_row_cells.view()
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
    let mut table_vec = Vec::new();
    table_vec.reserve((1 + steps) as usize);

    proof {
        table_vec.set_len((1 + steps) as usize);
    }
    
    table_vec.set(0, init.clone());

    let mut i: int = 0; // Represents the current step, from 0 to steps-1
    while i < steps
        invariant
            0 <= i <= steps,
            table_vec.len() == (1 + steps) as usize,
            table_vec.view().subsequence(0, (i + 1) as int).len() == (i + 1) as int, // Cast to int
            table_vec.view()[0] == init,
            forall|k: int| 0 <= k <= i ==> #[trigger] table_vec.view()[k].len() == init.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] table_vec.view()[k + 1] == compute_next_row(table_vec.view()[k], rule, init.len()),
    {
        let current_row = table_vec.view()[i];
        let next_row_val = compute_next_row(current_row, rule, init.len()); // Renamed variable
        table_vec.set((i + 1) as usize, next_row_val); // Use renamed variable
        i = i + 1;
    }
    table_vec.view()
}
// </vc-code>

fn main() {}

}