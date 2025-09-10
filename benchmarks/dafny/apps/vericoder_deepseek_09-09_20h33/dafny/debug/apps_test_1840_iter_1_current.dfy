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
lemma SumGoldForSpaceshipLemma(attacking_power: nat, bases: seq<(nat, nat)>, index: int)
    requires 0 <= index <= |bases|
    ensures SumGoldForSpaceship(attacking_power, bases) == 
        SumGoldForSpaceship(attacking_power, bases[index..]) + 
        (if index > 0 then SumGoldForSpaceship(attacking_power, bases[..index]) else 0)
    decreases |bases| - index
{
    if index == 0 {
        // Base case: empty prefix
    } else if index == |bases| {
        // Base case: empty suffix
    } else {
        // Recursive case: split at index
        SumGoldForSpaceshipLemma(attacking_power, bases, index + 1);
    }
}

lemma SumGoldForSpaceshipEmpty(attacking_power: nat)
    ensures SumGoldForSpaceship(attacking_power, []) == 0
{
}

lemma SumGoldForSpaceshipSplit(attacking_power: nat, bases: seq<(nat, nat)>, i: int)
    requires 0 <= i < |bases|
    ensures SumGoldForSpaceship(attacking_power, bases) == 
        SumGoldForSpaceship(attacking_power, bases[..i]) + 
        SumGoldForSpaceship(attacking_power, bases[i..])
    decreases |bases| - i
{
    SumGoldForSpaceshipLemma(attacking_power, bases, i);
}

lemma SumGoldForSpaceshipMonotonic(attacking_power1: nat, attacking_power2: nat, bases: seq<(nat, nat)>)
    requires attacking_power1 <= attacking_power2
    ensures SumGoldForSpaceship(attacking_power1, bases) <= SumGoldForSpaceship(attacking_power2, bases)
    decreases |bases|
{
    if |bases| == 0 {
    } else {
        SumGoldForSpaceshipMonotonic(attacking_power1, attacking_power2, bases[1..]);
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
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == SumGoldForSpaceship(attacking_powers[j], bases)
    {
        result := result + [SumGoldForSpaceship(attacking_powers[i], bases)];
        i := i + 1;
    }
}
// </vc-code>

