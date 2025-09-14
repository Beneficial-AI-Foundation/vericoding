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
// No changes needed in helpers
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
  table := [init];
  var i: nat := 1;
  while i <= steps
    invariant 1 <= i <= steps + 1
    invariant |table| == i
    invariant table[0] == init
    invariant forall k | 0 <= k < |table| :: |table[k]| == |init|
    invariant forall p | 0 <= p < |table| - 1 :: 
              forall q | 1 <= q <= |table[p]| - 2 :: table[p + 1][q] == rule(table[p][q - 1], table[p][q], table[p][q + 1])
    invariant forall p | 0 <= p < |table| - 1 :: 
              table[p + 1][0] == rule(false, table[p][0], table[p][1]) &&
              table[p + 1][|table[p]| - 1] == rule(table[p][|table[p]| - 2], table[p][|table[p]| - 1], false)
  {
    var prev := table[i - 1];
    var len := |prev|;
    var newRow: seq<bool> := [];
    var j: nat := 0;
    while j < len
      invariant 0 <= j <= len
      invariant |newRow| == j
      invariant forall q | 0 <= q < j :: newRow[q] == rule(
        if q == 0 then false else prev[q - 1],
        prev[q],
        if q == len - 1 then false else prev[q + 1]
      )
    {
      var left := if j == 0 then false else prev[j - 1];
      var center := prev[j];
      var right := if j == len - 1 then false else prev[j + 1];
      newRow := newRow + [rule(left, center, right)];
      j := j + 1;
    }
    table := table + [newRow];
    i := i + 1;
  }
}
// </vc-code>

