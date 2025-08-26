class Automaton {

/**
This method computes the automaton.
Provide the initial row: init, the rule and the desired number of steps
 */

// <vc-helpers>
function ApplyRule(prev: seq<bool>, rule: (bool, bool, bool) -> bool): seq<bool>
  requires |prev| >= 2
  ensures |ApplyRule(prev, rule)| == |prev|
  ensures forall j | 1 <= j <= |prev| - 2 :: ApplyRule(prev, rule)[j] == rule(prev[j - 1], prev[j], prev[j + 1])
  ensures ApplyRule(prev, rule)[0] == rule(false, prev[0], prev[1])
  ensures ApplyRule(prev, rule)[|prev| - 1] == rule(prev[|prev| - 2], prev[|prev| - 1], false)
{
  seq(|prev|, j =>
    if j == 0 then rule(false, prev[0], prev[1])
    else if j == |prev| - 1 then rule(prev[|prev| - 2], prev[|prev| - 1], false)
    else if 1 <= j <= |prev| - 2 then rule(prev[j - 1], prev[j], prev[j + 1])
    else false  // This case should never happen given the conditions above
  )
}

lemma BasicPropertiesLemma(table: seq<seq<bool>>, newRow: seq<bool>, init: seq<bool>, step: nat)
  requires |init| >= 2
  requires |table| == 1 + step
  requires table[0] == init
  requires forall i | 0 <= i < |table| :: |table[i]| == |init|
  requires |newRow| == |init|
  ensures var newTable := table + [newRow];
          |newTable| == 1 + step + 1 &&
          newTable[0] == init &&
          (forall i | 0 <= i < |newTable| :: |newTable[i]| == |init|)
{
  var newTable := table + [newRow];
}

lemma ExistingRowsLemma(table: seq<seq<bool>>, newRow: seq<bool>, rule: (bool, bool, bool) -> bool, step: nat)
  requires forall i | 0 <= i < |table| - 1 ::
             forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
  requires forall i | 0 <= i < |table| - 1 ::
             table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
  ensures var newTable := table + [newRow];
          (forall i | 0 <= i < |table| - 1 ::
             forall j | 1 <= j <= |newTable[i]| - 2 :: newTable[i + 1][j] == rule(newTable[i][j - 1], newTable[i][j], newTable[i][j + 1])) &&
          (forall i | 0 <= i < |table| - 1 ::
             newTable[i + 1][0] == rule(false, newTable[i][0], newTable[i][1]) && newTable[i + 1][|newTable[i]| - 1] == rule(newTable[i][|newTable[i]| - 2], newTable[i][|newTable[i]| - 1], false))
{
  var newTable := table + [newRow];
}

lemma NewRowLemma(table: seq<seq<bool>>, newRow: seq<bool>, rule: (bool, bool, bool) -> bool, step: nat)
  requires 0 <= step < |table|
  requires |table| == 1 + step
  requires forall i | 0 <= i < |table| :: |table[i]| == |table[0]|
  requires |table[0]| >= 2
  requires newRow == ApplyRule(table[step], rule)
  ensures var newTable := table + [newRow];
          forall j | 1 <= j <= |newTable[step]| - 2 :: newTable[step + 1][j] == rule(newTable[step][j - 1], newTable[step][j], newTable[step][j + 1])
  ensures var newTable := table + [newRow];
          newTable[step + 1][0] == rule(false, newTable[step][0], newTable[step][1]) && 
          newTable[step + 1][|newTable[step]| - 1] == rule(newTable[step][|newTable[step]| - 2], newTable[step][|newTable[step]| - 1], false)
{
  var newTable := table + [newRow];
  assert newTable[step] == table[step];
  assert newTable[step + 1] == newRow;
}

lemma ApplyRulePreservesInvariants(table: seq<seq<bool>>, rule: (bool, bool, bool) -> bool, step: nat, init: seq<bool>)
  requires |init| >= 2
  requires 0 <= step < |table|
  requires |table| == 1 + step
  requires table[0] == init
  requires forall i | 0 <= i < |table| :: |table[i]| == |init|
  requires forall i | 0 <= i < |table| - 1 ::
             forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
  requires forall i | 0 <= i < |table| - 1 ::
             table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
  ensures var newRow := ApplyRule(table[step], rule);
          var newTable := table + [newRow];
          |newTable| == 1 + step + 1 &&
          newTable[0] == init &&
          (forall i | 0 <= i < |newTable| :: |newTable[i]| == |init|) &&
          (forall i | 0 <= i < |newTable| - 1 ::
             forall j | 1 <= j <= |newTable[i]| - 2 :: newTable[i + 1][j] == rule(newTable[i][j - 1], newTable[i][j], newTable[i][j + 1])) &&
          (forall i | 0 <= i < |newTable| - 1 ::
             newTable[i + 1][0] == rule(false, newTable[i][0], newTable[i][1]) && newTable[i + 1][|newTable[i]| - 1] == rule(newTable[i][|newTable[i]| - 2], newTable[i][|newTable[i]| - 1], false))
{
  var newRow := ApplyRule(table[step], rule);
  
  BasicPropertiesLemma(table, newRow, init, step);
  ExistingRowsLemma(table, newRow, rule, step);
  NewRowLemma(table, newRow, rule, step);
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
  ensures table[0] == init
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
    var newRow := ApplyRule(table[step], rule);
    ApplyRulePreservesInvariants(table, rule, step, init);
    table := table + [newRow];
    step := step + 1;
  }
}
// </vc-code>

// example rule
function TheRule(a: bool, b: bool, c: bool) : bool
{
  a || b || c
}

// example rule 2
function TheRule2(a: bool, b: bool, c: bool) : bool
{
  a && b && c
}

}