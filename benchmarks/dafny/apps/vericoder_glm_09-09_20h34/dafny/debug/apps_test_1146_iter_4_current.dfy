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
lemma UnionLemma(m: nat, buttons: seq<seq<nat>>, n: nat)
    requires ValidInput(n, m, buttons)
    ensures CanTurnOnAllBulbs(m, buttons) <==> forall k :: 1 <= k <= m ==> exists i :: 0 <= i < |buttons| && k in buttons[i]
{
    calc ==> {
        CanTurnOnAllBulbs(m, buttons);
    ==  // def. CanTurnOnAllBulbs
        |unionOfAllBulbs(buttons)| == m;
    ==  // def. unionOfAllBulbs
        |set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j]| == m;
    == { 
        assert forall k :: 1 <= k <= m ==> k in set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j];
      }
        forall k :: 1 <= k <= m ==> k in set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j];
    ==  // def. set comprehension
        forall k :: 1 <= k <= m ==> exists i, j :: 0 <= i < |buttons| && 0 <= j < |buttons[i]| && buttons[i][j] == k;
    ==  // Can strengthen existential quantifier on j for an 'in' check.
        forall k :: 1 <= k <= m ==> exists i :: 0 <= i < |buttons| && k in buttons[i];
    }
    
    calc <== {
        forall k :: 1 <= k <= m ==> exists i :: 0 <= i < |buttons| && k in buttons[i];
    ==  // def. set comprehension
        forall k :: 1 <= k <= m ==> k in set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j];
    == { 
        assert forall k | 1 <= k <= m :: k in set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j];
        assert forall k :: k !in set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j] || k !in [1..m];
      }
        |set i, j | 0 <= i < |buttons| && 0 <= j < |buttons[i]| :: buttons[i][j]| == m;
    ==  // def. unionOfAllBulbs
        |unionOfAllBulbs(buttons)| == m;
    ==  // def. CanTurnOnAllBulbs
        CanTurnOnAllBulbs(m, buttons);
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
    var allBulbsCovered: bool := true;
    var k: nat := 1;
    
    while k <= m
        invariant 1 <= k <= m + 1
        invariant forall x :: 1 <= x < k ==> (exists i :: 0 <= i < n && x in buttons[i])
    {
        var found: bool := false;
        var i: nat := 0;
        
        while i < n && !found
            invariant 0 <= i <= n
            invariant found == (exists j :: 0 <= j < i && k in buttons[j])
        {
            if k in buttons[i] {
                found := true;
            }
            i := i + 1;
        }
        
        if !found {
            allBulbsCovered := false;
            break;
        }
        
        k := k + 1;
    }
    
    if allBulbsCovered {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

