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
function SumGoldForSpaceshipTail(attacking_power: nat, bases: seq<(nat, nat)>, acc: nat): nat
{
    if |bases| == 0 then acc
    else if attacking_power >= bases[0].0 then SumGoldForSpaceshipTail(attacking_power, bases[1..], acc + bases[0].1)
    else SumGoldForSpaceshipTail(attacking_power, bases[1..], acc)
}

lemma SumGoldForSpaceshipTailProperty(attacking_power: nat, bases: seq<(nat, nat)>, acc: nat)
    ensures SumGoldForSpaceshipTail(attacking_power, bases, acc) == SumGoldForSpaceship(attacking_power, bases) + acc
{
    if |bases| == 0 {
        // trivial
    } else {
        var head := bases[0];
        var tail := bases[1..];
        if attacking_power >= head.0 {
            calc {
                SumGoldForSpaceshipTail(attacking_power, bases, acc);
                SumGoldForSpaceshipTail(attacking_power, tail, acc + head.1);
                { SumGoldForSpaceshipTailProperty(attacking_power, tail, acc+head.1); }
                SumGoldForSpaceship(attacking_power, tail) + (acc + head.1);
                == (SumGoldForSpaceship(attacking_power, tail) + head.1) + acc;
                { assert SumGoldForSpaceship(attacking_power, tail) + head.1 == SumGoldForSpaceship(attacking_power, bases); }
                SumGoldForSpaceship(attacking_power, bases) + acc;
            }
        } else {
            calc {
                SumGoldForSpaceshipTail(attacking_power, bases, acc);
                SumGoldForSpaceshipTail(attacking_power, tail, acc);
                { SumGoldForSpaceshipTailProperty(attacking_power, tail, acc); }
                SumGoldForSpaceship(attacking_power, tail) + acc;
                { assert SumGoldForSpaceship(attacking_power, tail) == SumGoldForSpaceship(attacking_power, bases); }
                SumGoldForSpaceship(attacking_power, bases) + acc;
            }
        }
    }
}

lemma SumGoldForSpaceshipEq(attacking_power: nat, bases: seq<(nat, nat)>)
    ensures SumGoldForSpaceship(attacking_power, bases) == SumGoldForSpaceshipTail(attacking_power, bases, 0)
{
    SumGoldForSpaceshipTailProperty(attacking_power, bases, 0);
}
// </vc-helpers>

// <vc-spec>
method solve(s: nat, b: nat, attacking_powers: seq<nat>, bases: seq<(nat, nat)>) returns (result: seq<nat>)
    requires ValidInput(s, b, attacking_powers, bases)
    ensures ValidOutput(s, attacking_powers, bases, result)
// </vc-spec>
// <vc-code>
{
    var arr := new nat[s];
    var i := 0;
    while i < s
        invariant 0 <= i <= s
        invariant arr.Length == s
        invariant forall j :: 0 <= j < i ==> arr[j] == SumGoldForSpaceship(attacking_powers[j], bases)
        invariant forall j :: 0 <= j < i ==> arr[j] >= 0
    {
        arr[i] := SumGoldForSpaceshipTail(attacking_powers[i], bases, 0);
        SumGoldForSpaceshipEq(attacking_powers[i], bases);
        i := i + 1;
    }
    result := arr[..];
}
// </vc-code>

