Given n buttons and m bulbs, where each button can turn on a specific subset of bulbs,
determine if it's possible to turn on all m bulbs by pressing some combination of buttons.
Return "YES" if all bulbs can be turned on, "NO" otherwise.

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

method solve(n: nat, m: nat, buttons: seq<seq<nat>>) returns (result: string)
    requires ValidInput(n, m, buttons)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanTurnOnAllBulbs(m, buttons)
{
    var controllableBulbs: set<nat> := {};

    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant controllableBulbs == set k, l | 0 <= k < i && 0 <= l < |buttons[k]| :: buttons[k][l]
    {
        var j := 0;
        while j < |buttons[i]|
            invariant 0 <= j <= |buttons[i]|
            invariant controllableBulbs == (set k, l | 0 <= k < i && 0 <= l < |buttons[k]| :: buttons[k][l]) + (set l | 0 <= l < j :: buttons[i][l])
        {
            controllableBulbs := controllableBulbs + {buttons[i][j]};
            j := j + 1;
        }
        i := i + 1;
    }

    assert controllableBulbs == unionOfAllBulbs(buttons);

    if |controllableBulbs| == m {
        result := "YES";
    } else {
        result := "NO";
    }
}
