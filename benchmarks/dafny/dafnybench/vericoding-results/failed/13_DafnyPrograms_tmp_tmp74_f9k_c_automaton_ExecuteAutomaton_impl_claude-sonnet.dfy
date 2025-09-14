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
lemma TablePropertiesPreserved(table: seq<seq<bool>>, newRow: seq<bool>, init: seq<bool>)
  requires |table| >= 1
  requires table[0] == init
  requires |init| >= 2
  requires forall i | 0 <= i < |table| :: |table[i]| == |init|
  requires |newRow| == |init|
  ensures |table + [newRow]| == |table| + 1
  ensures (table + [newRow])[0] == init
  ensures forall i | 0 <= i < |table + [newRow]| :: |(table + [newRow])[i]| == |init|
{
}

lemma RuleApplicationCorrect(prevRow: seq<bool>, newRow: seq<bool>, rule: (bool, bool, bool) -> bool)
  requires |prevRow| >= 2
  requires |newRow| == |prevRow|
  requires newRow[0] == rule(false, prevRow[0], prevRow[1])
  requires newRow[|prevRow| - 1] == rule(prevRow[|prevRow| - 2], prevRow[|prevRow| - 1], false)
  requires forall j | 1 <= j <= |prevRow| - 2 :: newRow[j] == rule(prevRow[j - 1], prevRow[j], prevRow[j + 1])
  ensures forall j | 1 <= j <= |newRow| - 2 :: newRow[j] == rule(prevRow[j - 1], prevRow[j], prevRow[j + 1])
  ensures newRow[0] == rule(false, prevRow[0], prevRow[1]) && newRow[|prevRow| - 1] == rule(prevRow[|prevRow| - 2], prevRow[|prevRow| - 1], false)
{
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
  table := [init];
  
  var step := 0;
  while step < steps
    invariant 0 <= step <= steps
    invariant |table| == 1 + step
    invariant table[0] == init
    invariant forall i | 0 <= i < |table| :: |table[i]| == |init|
    invariant forall i | 0 <= i < |table| - 1 ::
                forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
    invariant forall i | 0 <= i < |table| - 1 ::
                table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
  {
    var prevRow := table[|table| - 1];
    var newRow := new bool[|init|];
    
    newRow[0] := rule(false, prevRow[0], prevRow[1]);
    newRow[|init| - 1] := rule(prevRow[|init| - 2], prevRow[|init| - 1], false);
    
    var j := 1;
    while j <= |init| - 2
      invariant 1 <= j <= |init| - 1
      invariant newRow[0] == rule(false, prevRow[0], prevRow[1])
      invariant newRow[|init| - 1] == rule(prevRow[|init| - 2], prevRow[|init| - 1], false)
      invariant forall k | 1 <= k < j :: newRow[k] == rule(prevRow[k - 1], prevRow[k], prevRow[k + 1])
    {
      newRow[j] := rule(prevRow[j - 1], prevRow[j], prevRow[j + 1]);
      j := j + 1;
    }
    
    var newRowSeq := newRow[..];
    TablePropertiesPreserved(table, newRowSeq, init);
    RuleApplicationCorrect(prevRow, newRowSeq, rule);
    table := table + [newRowSeq];
    step := step + 1;
  }
}
// </vc-code>

