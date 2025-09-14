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
method ComputeNextRow(current: seq<bool>, rule: (bool, bool, bool) -> bool) returns (next: seq<bool>)
  requires |current| >= 2
  ensures |next| == |current|
  ensures next[0] == rule(false, current[0], current[1])
  ensures next[|current| - 1] == rule(current[|current| - 2], current[|current| - 1], false)
  ensures forall j | 1 <= j <= |current| - 2 :: next[j] == rule(current[j - 1], current[j], current[j + 1])
{
  next := [];
  var i := 0;
  while i < |current|
    invariant 0 <= i <= |current|
    invariant |next| == i
    invariant i > 0 ==> next[0] == rule(false, current[0], current[1])
    invariant forall j | 1 <= j < i && j <= |current| - 2 :: next[j] == rule(current[j - 1], current[j], current[j + 1])
    invariant i == |current| ==> next[|current| - 1] == rule(current[|current| - 2], current[|current| - 1], false)
  {
    var left, center, right;
    center := current[i];
    
    if i == 0 {
      left := false;
      right := current[1];
    } else if i == |current| - 1 {
      left := current[i - 1];
      right := false;
    } else {
      left := current[i - 1];
      right := current[i + 1];
    }
    
    next := next + [rule(left, center, right)];
    i := i + 1;
  }
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
  var i := 0;
  
  while i < steps
    invariant 0 <= i <= steps
    invariant |table| == 1 + i
    invariant table[0] == init
    invariant forall k | 0 <= k < |table| :: |table[k]| == |init|
    invariant forall k | 0 <= k < |table| - 1 ::
              forall j | 1 <= j <= |table[k]| - 2 :: table[k + 1][j] == rule(table[k][j - 1], table[k][j], table[k][j + 1])
    invariant forall k | 0 <= k < |table| - 1 ::
              table[k + 1][0] == rule(false, table[k][0], table[k][1]) && 
              table[k + 1][|table[k]| - 1] == rule(table[k][|table[k]| - 2], table[k][|table[k]| - 1], false)
  {
    var nextRow := ComputeNextRow(table[|table| - 1], rule);
    table := table + [nextRow];
    i := i + 1;
  }
}
// </vc-code>

