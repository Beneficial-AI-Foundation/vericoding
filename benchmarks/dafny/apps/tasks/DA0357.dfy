// <vc-preamble>
predicate ValidInput(s: nat, b: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>)
{
    |attacking_powers| == s && |bases| == b
}

function SumGoldForSpaceship(attacking_power: nat, bases: seq<(nat, nat)>): nat
{
    if |bases| == 0 then 0
    else if attacking_power >= bases[0].0 then bases[0].1 + SumGoldForSpaceship(attacking_power, bases[1..])
    else SumGoldForSpaceship(attacking_power, bases[1..])
}

predicate ValidOutput(s: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>, result: seq<nat>)
{
    |result| == s &&
    (forall i :: 0 <= i < s ==> result[i] >= 0) &&
    (forall i :: 0 <= i < s && i < |attacking_powers| ==> result[i] == SumGoldForSpaceship(attacking_powers[i], bases))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: nat, b: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>) returns (result: seq<nat>)
    requires ValidInput(s, b, attacking_powers, bases)
    ensures ValidOutput(s, attacking_powers, bases, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
