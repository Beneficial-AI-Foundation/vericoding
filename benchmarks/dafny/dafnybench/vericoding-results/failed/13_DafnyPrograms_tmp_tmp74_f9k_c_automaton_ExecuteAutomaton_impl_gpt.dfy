/**
Consider cellular automata: a row of cells is repeatedly updated according to a rule. In this exercise I dabbled with,
each cell has the value either false or true. Each cell's next state depends only on the immediate neighbours, in the 
case where the cell is at the edges of the row, the inexistent neighbours are replaced by "false". The automaton table 
will contain the initial row, plus a row for each number of steps.
 */
class Automaton {

/**
This method computes the automaton.
Provide the initial row: init, the rule and the desired number of steps
 */

}

// <vc-helpers>
function NextRow(row: seq<bool>, rule: (bool, bool, bool) -> bool): seq<bool>
  requires |row| >= 2
  ensures |NextRow(row, rule)| == |row|
  ensures NextRow(row, rule)[0] == rule(false, row[0], row[1])
  ensures NextRow(row, rule)[|row| - 1] == rule(row[|row| - 2], row[|row| - 1], false)
  ensures forall j | 1 <= j <= |row| - 2 :: NextRow(row, rule)[j] == rule(row[j - 1], row[j], row[j + 1])
{
  seq(|row|, j =>
    if j == 0 then rule(false, row[0], row[1])
    else if j == |row| - 1 then rule(row[|row| - 2], row[|row| - 1], false)
    else rule(row[j - 1], row[j], row[j + 1]))
}

function Build(n: nat, row: seq<bool>, rule: (bool, bool, bool) -> bool): seq<seq<bool>>
  requires |row| >= 2
  ensures |Build(n, row, rule)| == 1 + n
  ensures Build(n, row, rule)[0] == row
  ensures forall i | 0 <= i < |Build(n, row, rule)| :: |Build(n, row, rule)[i]| == |row|
  ensures forall i | 0 <= i < |Build(n, row, rule)| - 1 ::
            Build(n, row, rule)[i + 1] == NextRow(Build(n, row, rule)[i], rule)
  decreases n
{
  if n == 0 then
    [row]
  else
    Build(n - 1, row, rule) +
    [NextRow(Build(n - 1, row, rule)[|Build(n - 1, row, rule)| - 1], rule)]
}
// </vc-helpers>

// <vc-spec>
method ExecuteAutomaton(init: seq<bool>, rule: (bool, bool, bool) -> bool, steps: nat)
  returns (table: seq<seq<bool>>)
  // we need the initial row to have the length bigger or equal to two
  requires |init| >= 2
  // after computation the automaton is made of the initial row plus a row for each of the steps
  ensures |table| == 1 + steps
  // the automaton must have the initial row at the top
  ensures table[0] == init;
  // all rows in the automaton must be the same length
  ensures forall i | 0 <= i < |table| :: |table[i]| == |init|
  // all the middle row elements (with existing neighbours) after a step, will be equal to the rule applied on the element in the previous state
  // and its neigbours
  ensures forall i | 0 <= i < |table| - 1 ::
            forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
  // the corner row elements (with non-existing neighbours) after a step, will be equal to the rule applied on the element in the previous state,
  // its neighbour and false
  ensures forall i | 0 <= i < |table| - 1 ::
            table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
// </vc-spec>
// <vc-code>
{
  table := Build(steps, init, rule);
}
// </vc-code>

