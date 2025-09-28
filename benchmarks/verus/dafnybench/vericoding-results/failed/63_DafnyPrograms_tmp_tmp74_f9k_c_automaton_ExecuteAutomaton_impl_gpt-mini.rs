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
// <vc-helpers>
// No helpers needed for this implementation.
 // </vc-helpers>
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
    let n: nat = init.len();

    let mut table_v: Vec<Seq<bool>> = Vec::new();
    table_v.push(init);

    let mut prev: Seq<bool> = table_v.index(0);
    let mut i: nat = 0;
    while i < steps
        invariant i <= steps;
        invariant table_v.len() == 1 + i;
        invariant prev.len() == n;
        decreases steps - i;
    {
        let mut next_v: Vec<bool> = Vec::new();
        let mut j: nat = 0;
        while j < n
            invariant j <= n && next_v.len() == j;
            decreases n - j;
        {
            let left: bool;
            let center: bool;
            let right: bool;

            if j == 0 {
                left = false;
                center = prev@[0];
                right = prev@[1];
            } else if j + 1 == n {
                left = prev@[j - 1];
                center = prev@[j];
                right = false;
            } else {
                left = prev@[j - 1];
                center = prev@[j];
                right = prev@[j + 1];
            }

            next_v.push(rule(left, center, right));
            j = j + 1;
        }

        let next_seq: Seq<bool> = next_v.into_seq();
        table_v.push(next_seq);
        prev = table_v.index(table_v.len() - 1);
        i = i + 1;
    }

    let table: Seq<Seq<bool>> = table_v.into_seq();

    // Postconditions proof obligations
    assert(table.len() == 1 + steps);
    assert(table@[0] == init);
    // all rows same length
    let mut k: nat = 0;
    while k < table.len()
        invariant k <= table.len();
        invariant forall|kk: nat| kk < k ==> #[trigger] table@[kk].len() == n;
        decreases table.len() - k;
    {
        assert(table@[k].len() == n);
        k = k + 1;
    }

    table
}
// </vc-code>

fn main() {}

}