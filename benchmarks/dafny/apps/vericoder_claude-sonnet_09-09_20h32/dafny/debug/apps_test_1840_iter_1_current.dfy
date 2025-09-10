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

// <vc-helpers>
lemma SumGoldForSpaceshipNonNegative(attacking_power: nat, bases: seq<(nat, nat)>)
    ensures SumGoldForSpaceship(attacking_power, bases) >= 0
{
    if |bases| == 0 {
    } else if attacking_power >= bases[0].0 {
        SumGoldForSpaceshipNonNegative(attacking_power, bases[1..]);
    } else {
        SumGoldForSpaceshipNonNegative(attacking_power, bases[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: nat, b: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>) returns (result: seq<nat>)
    requires ValidInput(s, b, attacking_powers, bases)
    ensures ValidOutput(s, attacking_powers, bases, result)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < s
        invariant 0 <= i <= s
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] >= 0
        invariant forall j :: 0 <= j < i && j < |attacking_powers| ==> result[j] == SumGoldForSpaceship(attacking_powers[j], bases)
    {
        SumGoldForSpaceshipNonNegative(attacking_powers[i], bases);
        var gold := SumGoldForSpaceship(attacking_powers[i], bases);
        result := result + [gold];
        i := i + 1;
    }
}
// </vc-code>

