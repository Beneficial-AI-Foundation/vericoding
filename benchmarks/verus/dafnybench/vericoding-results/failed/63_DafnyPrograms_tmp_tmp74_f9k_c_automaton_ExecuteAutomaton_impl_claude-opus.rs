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
// Helper function to compute the next row based on the current row and rule
spec fn compute_next_row(current: Seq<bool>, rule: spec_fn(bool, bool, bool) -> bool) -> Seq<bool>
    recommends current.len() >= 2
{
    Seq::new(current.len(), |j: int| {
        if j == 0 {
            rule(false, current[0], current[1])
        } else if j == current.len() - 1 {
            rule(current[current.len() - 2], current[current.len() - 1], false)
        } else {
            rule(current[j - 1], current[j], current[j + 1])
        }
    })
}

// Helper to build the complete automaton table
spec fn build_automaton(init: Seq<bool>, rule: spec_fn(bool, bool, bool) -> bool, steps: nat) -> Seq<Seq<bool>>
    recommends init.len() >= 2
    decreases steps
{
    if steps == 0 {
        seq![init]
    } else {
        let prev_table = build_automaton(init, rule, (steps - 1) as nat);
        let last_row = prev_table[prev_table.len() - 1];
        let next_row = compute_next_row(last_row, rule);
        prev_table.push(next_row)
    }
}

// Lemma to prove properties about the automaton table
proof fn automaton_properties(init: Seq<bool>, rule: spec_fn(bool, bool, bool) -> bool, steps: nat)
    requires init.len() >= 2
    ensures 
        build_automaton(init, rule, steps).len() == 1 + steps,
        build_automaton(init, rule, steps)[0] == init,
        forall|i: int| 0 <= i < build_automaton(init, rule, steps).len() ==> 
            #[trigger] build_automaton(init, rule, steps)[i].len() == init.len()
    decreases steps
{
    if steps == 0 {
        assert(build_automaton(init, rule, 0) == seq![init]);
    } else {
        automaton_properties(init, rule, (steps - 1) as nat);
        let prev_table = build_automaton(init, rule, (steps - 1) as nat);
        let table = build_automaton(init, rule, steps);
        assert(table.len() == prev_table.len() + 1);
        assert(table[0] == init);
        
        // Prove all rows have the same length
        assert forall|i: int| 0 <= i < prev_table.len() implies 
            #[trigger] prev_table[i].len() == init.len() by {
            automaton_properties(init, rule, (steps - 1) as nat);
        }
        
        let last_row = prev_table[prev_table.len() - 1];
        let next_row = compute_next_row(last_row, rule);
        assert(next_row.len() == last_row.len());
        assert(table[table.len() - 1] == next_row);
    }
}

// Helper function to convert Vec<Vec<bool>> view to Seq<Seq<bool>>
spec fn vec_vec_to_seq_seq(v: Seq<Vec<bool>>) -> Seq<Seq<bool>> {
    Seq::new(v.len(), |i: int| v[i]@)
}

// Exec version of compute_next_row for use in implementation
fn compute_next_row_exec(current: &Vec<bool>, rule: spec_fn(bool, bool, bool) -> bool) -> (next_row: Vec<bool>)
    requires current.len() >= 2
    ensures 
        next_row@ == compute_next_row(current@, rule),
        next_row.len() == current.len()
{
    let mut next_row: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < current.len()
        invariant
            current@.len() == current.len(),
            current.len() >= 2,
            j <= current.len(),
            next_row.len() == j,
            forall|k: int| 0 <= k < j ==> next_row@[k] == compute_next_row(current@, rule)[k]
    {
        let val = if j == 0 {
            rule(false, current[0], current[1])
        } else if j == current.len() - 1 {
            rule(current[current.len() - 2], current[current.len() - 1], false)
        } else {
            rule(current[j - 1], current[j], current[j + 1])
        };
        next_row.push(val);
        j = j + 1;
    }
    assert(next_row@ == compute_next_row(current@, rule));
    next_row
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
    // The input should already be a Seq, but we need to work with Vecs in exec code
    // We'll build the table directly without converting from Seq first
    let mut table: Vec<Vec<bool>> = Vec::new();
    
    // Build initial row as Vec from the Seq specification
    let ghost init_spec = init;
    let mut init_vec: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    let init_len = init_spec.len() as usize;
    
    // Use a ghost variable to access the spec Seq
    while k < init_len
        invariant
            init_len == init_spec.len(),
            k <= init_len,
            init_vec.len() == k,
            forall|j: int| 0 <= j < k ==> init_vec@[j] == init_spec[j]
    {
        // We need to construct the Vec element by element
        // Since we can't directly index into init_spec in exec code,
        // we use a spec expression that the verifier can understand
        let ghost val_spec = init_spec[k as int];
        let val: bool = if k == 0 && init_spec[0] { true } 
                       else if k == 0 && !init_spec[0] { false }
                       else if k > 0 && k < init_len && init_spec[k as int] { true }
                       else { false };
        
        // Assert that we got the right value
        proof {
            if k == 0 {
                assert(val == init_spec[0]);
            } else {
                assert(val == init_spec[k as int]);
            }
        }
        
        init_vec.push(val);
        k = k + 1;
    }
    
    assert(init_vec@ == init_spec);
    table.push(init_vec);
    
    let mut i: usize = 0;
    let steps_usize = steps as usize;
    
    while i < steps_usize
        invariant
            steps_usize == steps,
            i <= steps_usize,
            table.len() == 1 + i,
            table@[0]@ == init_spec,
            forall|j: int| 0 <= j < table.len() ==> #[trigger] table@[j]@.len() == init_spec.len(),
            vec_vec_to_seq_seq(table@) == build_automaton(init_spec, rule, i as nat)
    {
        let current_row = &table[i];
        let next_row = compute_next_row_exec(current_row, rule);
        
        assert(next_row@ == compute_next_row(current_row@, rule));
        table.push(next_row);
        i = i + 1;
    }
    
    proof {
        automaton_properties(init_spec, rule, steps);
        assert(vec_vec_to_seq_seq(table@) == build_automaton(init_spec, rule, steps));
    }
    
    // Convert Vec<Vec<bool>> to Seq<Seq<bool>> for return
    vec_vec_to_seq_seq(table@)
}
// </vc-code>

fn main() {}

}