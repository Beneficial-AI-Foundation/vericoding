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
lemma UnionSizeProperty(m: nat, buttons: seq<seq<nat>>)
    requires forall i :: 0 <= i < |buttons| ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
    ensures |unionOfAllBulbs(buttons)| <= m

function collectAllBulbs(buttons: seq<seq<nat>>, i: nat): set<nat>
    requires i <= |buttons|
{
    if i == 0 then {}
    else collectAllBulbs(buttons, i-1) + set j | 0 <= j < |buttons[i-1]| :: buttons[i-1][j]
}

lemma CollectAllBulbsCorrect(buttons: seq<seq<nat>>)
    ensures collectAllBulbs(buttons, |buttons|) == unionOfAllBulbs(buttons)
{
    if |buttons| == 0 {
        assert unionOfAllBulbs(buttons) == {};
    } else {
        CollectAllBulbsCorrect(buttons[..|buttons|-1]);
        assert buttons == buttons[..|buttons|-1] + [buttons[|buttons|-1]];
    }
}

function countUniqueBulbs(buttons: seq<seq<nat>>, seen: set<nat>, i: nat): nat
    requires i <= |buttons|
    decreases |buttons| - i
{
    if i == |buttons| then |seen|
    else 
        var newSeen := seen + set j | 0 <= j < |buttons[i]| :: buttons[i][j];
        countUniqueBulbs(buttons, newSeen, i + 1)
}

lemma CountUniqueBulbsCorrect(buttons: seq<seq<nat>>, m: nat)
    requires forall i :: 0 <= i < |buttons| ==> forall j :: 0 <= j < |buttons[i]| ==> 1 <= buttons[i][j] <= m
    ensures countUniqueBulbs(buttons, {}, 0) == |unionOfAllBulbs(buttons)|
{
    CountUniqueBulbsHelper(buttons, {}, 0);
}

lemma CountUniqueBulbsHelper(buttons: seq<seq<nat>>, seen: set<nat>, i: nat)
    requires i <= |buttons|
    decreases |buttons| - i
    ensures countUniqueBulbs(buttons, seen, i) == |seen + unionOfAllBulbs(buttons[i..])|
{
    if i == |buttons| {
        assert buttons[i..] == [];
        assert unionOfAllBulbs([]) == {};
    } else {
        var newSeen := seen + set j | 0 <= j < |buttons[i]| :: buttons[i][j];
        CountUniqueBulbsHelper(buttons, newSeen, i + 1);
        assert buttons[i..] == [buttons[i]] + buttons[i+1..];
        assert unionOfAllBulbs(buttons[i..]) == 
               (set j | 0 <= j < |buttons[i]| :: buttons[i][j]) + unionOfAllBulbs(buttons[i+1..]);
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
    var uniqueCount := countUniqueBulbs(buttons, {}, 0);
    CountUniqueBulbsCorrect(buttons, m);
    
    if uniqueCount == m {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

