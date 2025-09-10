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

// <vc-helpers>
lemma UnionContainsAllBulbs(buttons: seq<seq<nat>>, m: nat)
    requires ValidInput(|buttons|, m, buttons)
    requires 1 <= m
    ensures forall bulb :: 1 <= bulb <= m && bulb in unionOfAllBulbs(buttons) ==>
             bulb in unionOfAllBulbs(buttons)
{
}

lemma SetCardinalityProperty(s: set<nat>, m: nat)
    requires |s| == m
    ensures forall x :: x in s ==> 1 <= x <= m
{
}

lemma ValidInputImpliesBulbsInRange(buttons: seq<seq<nat>>, m: nat)
    requires ValidInput(|buttons|, m, buttons)
    ensures forall x :: x in unionOfAllBulbs(buttons) ==> 1 <= x <= m
{
    forall x | x in unionOfAllBulbs(buttons)
        ensures 1 <= x <= m
    {
        var i :| 0 <= i < |buttons| && exists j :: 0 <= j < |buttons[i]| && buttons[i][j] == x;
        var j :| 0 <= j < |buttons[i]| && buttons[i][j] == x;
        assert ValidInput(|buttons|, m, buttons);
        assert forall i2 :: 0 <= i2 < |buttons| ==> forall j2 :: 0 <= j2 < |buttons[i2]| ==> 1 <= buttons[i2][j2] <= m;
        assert 1 <= buttons[i][j] <= m;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, buttons: seq<seq<nat>>) returns (result: string)
    requires ValidInput(n, m, buttons)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanTurnOnAllBulbs(m, buttons)
// </vc-spec>
// <vc-code>
{
    ValidInputImpliesBulbsInRange(buttons, m);
    var bulbSet := unionOfAllBulbs(buttons);
    SetCardinalityProperty(bulbSet, m);
    if |bulbSet| == m {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

