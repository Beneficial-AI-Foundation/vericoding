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
lemma UnionSizeUpperBound(m: nat, buttons: seq<seq<nat>>)
    requires forall i :: 0 <= i < |buttons| ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
    ensures |unionOfAllBulbs(buttons)| <= m
{
    var s := unionOfAllBulbs(buttons);
    assert forall x :: x in s ==> 1 <= x <= m;
}

lemma UnionContainsElement(buttons: seq<seq<nat>>, i: nat, j: nat)
    requires 0 <= i < |buttons|
    requires 0 <= j < |buttons[i]|
    ensures buttons[i][j] in unionOfAllBulbs(buttons)
{
}

lemma UnionSubsetImpliesNotAllBulbs(m: nat, buttons: seq<seq<nat>>, missing: nat)
    requires m >= 1
    requires forall i :: 0 <= i < |buttons| ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
    requires 1 <= missing <= m
    requires missing !in unionOfAllBulbs(buttons)
    ensures |unionOfAllBulbs(buttons)| < m
{
    UnionSizeUpperBound(m, buttons);
}

function unionUpTo(buttons: seq<seq<nat>>, i: nat): set<nat>
    requires 0 <= i <= |buttons|
{
    set x, j | 0 <= x < i && 0 <= j < |buttons[x]| :: buttons[x][j]
}

function unionUpToWithPartial(buttons: seq<seq<nat>>, i: nat, j: nat): set<nat>
    requires 0 <= i < |buttons|
    requires 0 <= j <= |buttons[i]|
{
    unionUpTo(buttons, i) + set k | 0 <= k < j :: buttons[i][k]
}

lemma UnionUpToSubset(buttons: seq<seq<nat>>, i: nat)
    requires 0 <= i <= |buttons|
    ensures unionUpTo(buttons, i) <= unionOfAllBulbs(buttons)
{
}

lemma UnionUpToComplete(buttons: seq<seq<nat>>)
    ensures unionUpTo(buttons, |buttons|) == unionOfAllBulbs(buttons)
{
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
    var allBulbs: set<nat> := {};
    var i := 0;
    
    while i < |buttons|
        invariant 0 <= i <= |buttons|
        invariant allBulbs == unionUpTo(buttons, i)
        invariant allBulbs <= unionOfAllBulbs(buttons)
    {
        var j := 0;
        while j < |buttons[i]|
            invariant 0 <= j <= |buttons[i]|
            invariant allBulbs == unionUpToWithPartial(buttons, i, j)
        {
            allBulbs := allBulbs + {buttons[i][j]};
            j := j + 1;
        }
        i := i + 1;
    }
    
    assert allBulbs == unionOfAllBulbs(buttons) by {
        UnionUpToComplete(buttons);
    }
    
    if |allBulbs| == m {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

