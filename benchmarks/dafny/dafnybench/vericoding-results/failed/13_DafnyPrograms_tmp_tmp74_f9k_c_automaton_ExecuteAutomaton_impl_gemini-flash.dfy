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
function ComputeNextRow(prevRow: seq<bool>, rule: (bool, bool, bool) -> bool): seq<bool>
  requires |prevRow| >= 2
  ensures |ComputeNextRow(prevRow, rule)| == |prevRow|
  ensures forall j | 1 <= j <= |prevRow| - 2 :: ComputeNextRow(prevRow, rule)[j] == rule(prevRow[j - 1], prevRow[j], prevRow[j + 1])
  ensures ComputeNextRow(prevRow, rule)[0] == rule(false, prevRow[0], prevRow[1])
  ensures ComputeNextRow(prevRow, rule)[|prevRow| - 1] == rule(prevRow[|prevRow| - 2], prevRow[|prevRow| - 1], false)
{
  var len := |prevRow|;
  var newRowSeq: seq<bool> := [];

  for j := 0 to len - 1
    invariant 0 <= j <= len
    invariant |newRowSeq| == j
    invariant forall k | 1 <= k < j && k <= len - 2 :: newRowSeq[k] == rule(prevRow[k - 1], prevRow[k], prevRow[k + 1])
    invariant j > 0 ==> newRowSeq[0] == rule(false, prevRow[0], prevRow[1])
    invariant j == len ==> newRowSeq[len-1] == rule(prevRow[len - 2], prevRow[len - 1], false)
  {
    if j == 0 {
      newRowSeq := newRowSeq + [rule(false, prevRow[0], prevRow[1])];
    } else if j == len - 1 {
      newRowSeq := newRowSeq + [rule(prevRow[len - 2], prevRow[len - 1], false)];
    } else {
      newRowSeq := newRowSeq + [rule(prevRow[j - 1], prevRow[j], prevRow[j + 1])];
    }
  }
  return newRowSeq;
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
  var table: seq<seq<bool>> := [init];
  var currentRow := init;

  for i := 0 to steps - 1
    decreases steps - i
    invariant 0 <= i <= steps
    invariant |table| == 1 + i
    invariant table[0] == init
    invariant currentRow == table[i]
    invariant forall k | 0 <= k < |table| :: |table[k]| == |init|
    invariant forall k | 0 <= k < i ::
              forall j | 1 <= j <= |table[k]| - 2 :: table[k+1][j] == rule(table[k][j - 1], table[k][j], table[k][j + 1])
    invariant forall k | 0 <= k < i ::
              table[k+1][0] == rule(false, table[k][0], table[k][1]) && table[k+1][|table[k]| - 1] == rule(table[k][|table[k]| - 2], table[k][|table[k]| - 1], false)
    invariant forall k | 0 <= k < i :: ComputeNextRow(table[k], rule) == table[k+1]
  {
    currentRow := ComputeNextRow(currentRow, rule);
    table := table + [currentRow];
  }
  return table;
}
// </vc-code>

