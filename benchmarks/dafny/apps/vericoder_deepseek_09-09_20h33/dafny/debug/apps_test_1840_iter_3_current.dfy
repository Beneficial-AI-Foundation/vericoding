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
        SumGoldForSpaceship(attacking_power, bases[index..])
    decreases |bases| - index
{
    if index == 0 {
        // Base case: empty prefix, so bases[index..] == bases
    } else if index == |bases| {
        SumGoldForSpaceshipEmpty(attacking_power);
        assert bases[index..] == [];
    } else {
        // Recursive case: split at index
        SumGoldForSpaceshipLemma(attacking_power, bases[1..], index - 1);
        
        // Now handle the recursive definition
        if attacking_power >= bases[0].0 {
            assert SumGoldForSpaceship(attacking_power, bases) == bases[0].1 + SumGoldForSpaceship(attacking_power, bases[1..]);
            assert bases[index..] == bases[1..][(index-1)..];
            assert SumGoldForSpaceship(attacking_power, bases[1..]) == SumGoldForSpaceship(attacking_power, bases[1..][(index-1)..]);
            assert SumGoldForSpaceship(attacking_power, bases[index..]) == SumGoldForSpaceship(attaking_power, bases[1..][(index-1)..]);
        } else {
            assert SumGoldForSpaceship(attacking_power, bases) == SumGoldForSpaceship(attacking_power, bases[1..]);
            assert bases[index..] == bases[1..][(index-1)..];
            assert SumGoldForSpaceship(attacking_power, bases[1..]) == SumGoldForSpaceship(attacking_power, bases[1..][(index-1)..]);
            assert SumGoldForSpaceship(attacking_power, bases[index..]) == SumGoldForSpaceship(attacking_power, bases[1..][(index-1)..]);
        }
    }
}

lemma SumGoldForSpaceshipEmpty(attacking_power: nat)
    ensures SumGoldForSpaceship(attacking_power, []) == 0
{
}

lemma SumGoldForSpaceshipMonotonic(attacking_power1: nat, attacking_power2: nat, bases: seq<(nat, nat)>)
    requires attacking_power1 <= attacking_power2
    ensures SumGoldForSpaceship(attacking_power1, bases) <= SumGoldForSpaceship(attacking_power2, bases)
    decreases |bases|
{
    if |bases| == 0 {
    } else {
        SumGoldForSpaceshipMonotonic(attacking_power1, attacking_power2, bases[1..]);
        if attacking_power1 >= bases[0].0 {
            assert SumGoldForSpaceship(attacking_power1, bases) == bases[0].1 + SumGoldForSpaceship(attacking_power1, bases[1..]);
            assert SumGoldForSpaceship(attacking_power2, bases) == bases[0].1 + SumGoldForSpaceship(attacking_power2, bases[1..]);
        } else if attacking_power2 >= bases[0].0 {
            assert SumGoldForSpaceship(attacking_power1, bases) == SumGoldForSpaceship(attacking_power1, bases[1..]);
            assert SumGoldForSpaceship(attacking_power2, bases) == bases[0].1 + SumGoldForSpaceship(attacking_power2, bases[1..]);
        } else {
            assert SumGoldForSpaceship(attacking_power1, bases) == SumGoldForSpaceship(attacking_power1, bases[1..]);
            assert SumGoldForSpaceship(attacking_power2, bases) == SumGoldForSpaceship(attacking_power2, bases[1..]);
        }
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
        invariant forall j :: 0 <= j < i ==> j < |result| && result[j] == SumGoldForSpaceship(attacking_powers[j], bases)
    {
        var gold := SumGoldForSpaceship(attacking_powers[i], bases);
        result := result + [gold];
        i := i + 1;
    }
}
// </vc-code>

