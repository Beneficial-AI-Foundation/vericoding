// <vc-preamble>
class Automaton {

}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Resubmitting correct implementation; compilation error is in non-editable spec. */
function NextState(current: seq<bool>, rule: (bool, bool, bool) -> bool): seq<bool>
  requires |current| >= 2
{
  seq(|current|, j =>
    if 1 <= j < |current| - 1 then
      rule(current[j - 1], current[j], current[j + 1])
    else if j == 0 then
      rule(false, current[0], current[1])
    else // j == |current| - 1
      rule(current[|current| - 2], current[|current| - 1], false)
  )
}
// </vc-helpers>

// <vc-spec>
method ExecuteAutomaton(init: seq<bool>, rule: (bool, bool, bool) -> bool, steps: nat)
  returns (table: seq<seq<bool>>)

  requires |init| >= 2

  ensures |table| == 1 + steps

  ensures table[0] == init;

  ensures forall i | 0 <= i < |table| :: |table[i]| == |init|

  ensures forall i | 0 <= i < |table| - 1 ::
            forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])

  ensures forall i | 0 <= i < |table| - 1 ::
            table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Resubmitting correct implementation; compilation error is in non-editable spec. */
  table := [init];
  var i := 0;
  while i < steps
    invariant 0 <= i <= steps
    invariant |table| == i + 1
    invariant table[0] == init
    invariant forall k | 0 <= k < |table| :: |table[k]| == |init|
    invariant forall k | 0 <= k < i :: table[k+1] == NextState(table[k], rule)
  {
    var next_row := NextState(table[i], rule);
    table := table + [next_row];
    i := i + 1;
  }
}
// </vc-code>
