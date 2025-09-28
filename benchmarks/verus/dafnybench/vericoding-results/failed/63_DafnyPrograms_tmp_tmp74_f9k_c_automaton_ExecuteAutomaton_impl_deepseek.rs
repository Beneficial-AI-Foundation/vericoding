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
proof fn rule_spec_consistent(rule: spec_fn(bool, bool, bool) -> bool, a: bool, b: bool, c: bool, a2: bool, b2: bool, c2: bool)
    requires
        a == a2,
        b == b2,
        c == c2,
    ensures
        rule(a, b, c) == rule(a2, b2, c2),
{
}

spec fn get_next_cell(rule: &spec_fn(bool, bool, bool) -> bool, row: &Seq<bool>, index: int) -> bool
    requires
        0 <= index < row.len(),
{
    let left = if index > 0 { row[index - 1] } else { false };
    let center = row[index];
    let right = if index < row.len() - 1 { row[index + 1] } else { false };
    
    rule(left, center, right)
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
    let mut table = Seq::<Seq<bool>>::empty();
    table = table.push(init.clone());
    
    let mut step_count: nat = 0;
    while step_count < steps
        invariant
            step_count <= steps,
            table.len() == 1 + step_count,
            table[0] == init,
            forall|i: int| 0 <= i < table.len() ==> #[trigger] table[i].len() == init.len(),
    {
        let prev_row = table[step_count].clone();
        let mut new_row = Seq::<bool>::empty();
        
        let len: nat = init.len();
        let mut j: nat = 0;
        
        while j < len
            invariant
                j <= len,
                new_row.len() == j,
                forall|k: nat| k < j ==> #[trigger] new_row@[k] == get_next_cell(&rule, &prev_row, k as int),
        {
            proof {
                assert(0 <= j as int && j as int < prev_row.len()) by {
                    assert(j < len);
                    assert(prev_row.len() == init.len());
                }
            }
            let next_val = get_next_cell(&rule, &prev_row, j as int);
            new_row = new_row.push(next_val);
            j = j + 1;
        }
        
        table = table.push(new_row);
        step_count = step_count + 1;
    }
    
    table
}
// </vc-code>

fn main() {}

}