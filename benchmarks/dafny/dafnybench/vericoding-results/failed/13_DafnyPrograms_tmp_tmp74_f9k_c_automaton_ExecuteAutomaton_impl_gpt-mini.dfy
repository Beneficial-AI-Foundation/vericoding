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
method NextRow(prev: seq<bool>, rule: (bool, bool, bool) -> bool) returns (next: seq<bool>)
  requires |prev| >= 2
  ensures |next| == |prev|
  ensures next[0] == rule(false, prev[0], prev[1])
  ensures next[|prev|-1] == rule(prev[|prev|-2], prev[|prev|-1], false)
  ensures forall j | 1 <= j <= |prev|-2 :: next[j] == rule(prev[j-1], prev[j], prev[j+1])
{
  var a := new bool[|prev|];
  // handle first element
  a[0] := rule(false, prev[0], prev[1]);
  // fill middle elements
  var j := 1;
  while j <= |prev| - 2
    invariant 1 <= j <= |prev| - 1
    invariant a[0] == rule(false, prev[0], prev[1])
    invariant forall i | 1 <= i < j :: a[i] == rule(prev[i-1], prev[i], prev[i+1])
  {
    a[j] := rule(prev[j-1], prev[j], prev[j+1]);
    j := j + 1;
  }
  // handle last element
  a[|prev| - 1] := rule(prev[|prev| - 2], prev[|prev| - 1], false);
  next := a[..];
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
  var n := |init|;
  var t := [init];
  var k := 0;
  while k < steps
    invariant 0 <= k <= steps
    invariant |t| == 1 + k
    invariant forall i | 0 <= i < |t| :: |t[i]| == n
    invariant t[0] == init
    invariant forall i | 0 <= i < k ::
                forall j | 1 <= j <= n-2 :: t[i + 1][j] == rule(t[i][j - 1], t[i][j], t[i][j + 1])
    invariant forall i | 0 <= i < k :: t[i + 1][0] == rule(false, t[i][0], t[i][1]) && t[i + 1][n - 1] == rule(t[i][n - 2], t[i][n - 1], false)
  {
    var prev := t[|t| - 1];
    var next := NextRow(prev, rule);
    t := t + [next];
    k := k + 1;
  }
  return t;
}
// </vc-code>

