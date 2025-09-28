// <vc-preamble>
predicate ValidInput(n: nat, m: nat, buttons: seq<seq<nat>>)
{
    |buttons| == n &&
    n >= 1 && m >= 1 &&
    forall i :: 0 <= i < n ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
}

function unionOfAllBulbs(buttons: seq<seq<nat>>): set<nat>
{
    set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j]
}

predicate CanTurnOnAllBulbs(m: nat, buttons: seq<seq<nat>>)
{
    |unionOfAllBulbs(buttons)| == m
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed 'method' keyword from function declaration to fix compilation error. */
function ComputeResult(m: nat, buttons: seq<seq<nat>>): string
{
    if CanTurnOnAllBulbs(m, buttons) then "YES" else "NO"
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, buttons: seq<seq<nat>>) returns (result: string)
    requires ValidInput(n, m, buttons)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanTurnOnAllBulbs(m, buttons)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Calling the fixed helper function to compute the result. */
{
  result := ComputeResult(m, buttons);
}
// </vc-code>
