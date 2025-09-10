function winner(a: char, b: char): char
{
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') then b else a
}

predicate validRPSChar(c: char)
{
    c == 'R' || c == 'P' || c == 'S'
}

predicate validRPSString(s: string)
{
    forall i :: 0 <= i < |s| ==> validRPSChar(s[i])
}

predicate ValidInput(n: int, k: int, s: string)
{
    n > 0 && k >= 0 && |s| == n && validRPSString(s)
}

// <vc-helpers>
function simulateRound(s: string): string
    requires |s| > 0
    requires validRPSString(s)
    ensures |simulateRound(s)| == (|s| + 1) / 2
    ensures validRPSString(simulateRound(s))
{
    if |s| == 1 then s
    else if |s| == 2 then [winner(s[0], s[1])]
    else [winner(s[0], s[1])] + simulateRound(s[2..])
}

function simulateKRounds(s: string, k: nat): string
    requires |s| > 0
    requires validRPSString(s)
    ensures |simulateKRounds(s, k)| > 0
    ensures validRPSString(simulateKRounds(s, k))
    decreases k
{
    if k == 0 || |s| == 1 then s
    else simulateKRounds(simulateRound(s), k - 1)
}

lemma SimulateKRoundsProperties(s: string, k: nat)
    requires |s| > 0
    requires validRPSString(s)
    ensures |simulateKRounds(s, k)| >= 1
    ensures validRPSString(simulateKRounds(s, k))
    decreases k
{
    // Proof by induction on k
    if k == 0 || |s| == 1 {
        // Base case: trivial
    } else {
        var nextRound := simulateRound(s);
        assert |nextRound| == (|s| + 1) / 2;
        assert |nextRound| > 0;
        assert validRPSString(nextRound);
        SimulateKRoundsProperties(nextRound, k - 1);
    }
}

lemma SimulateRoundEquivalence(s: string, next: string)
    requires |s| > 0
    requires validRPSString(s)
    requires |next| == (|s| + 1) / 2
    requires validRPSString(next)
    requires forall j :: 0 <= j < (|s| / 2) ==> next[j] == winner(s[2*j], s[2*j+1])
    requires |s| % 2 == 1 ==> next[|next| - 1] == s[|s| - 1]
    ensures next == simulateRound(s)
{
    if |s| == 1 {
        assert next == s;
    } else if |s| == 2 {
        assert next == [winner(s[0], s[1])];
    } else {
        var expected := simulateRound(s);
        assert expected[0] == winner(s[0], s[1]);
        assert next[0] == winner(s[0], s[1]);
        
        var restNext := next[1..];
        var restS := s[2..];
        
        assert |restNext| == (|restS| + 1) / 2;
        assert validRPSString(restNext);
        assert forall j :: 0 <= j < (|restS| / 2) ==> restNext[j] == winner(restS[2*j], restS[2*j+1]);
        assert |restS| % 2 == 1 ==> restNext[|restNext| - 1] == restS[|restS| - 1];
        
        SimulateRoundEquivalence(restS, restNext);
        assert restNext == simulateRound(restS);
        assert next == [winner(s[0], s[1])] + restNext;
        assert expected == [winner(s[0], s[1])] + simulateRound(s[2..]);
    }
}

lemma SimulateKRoundsStep(s: string, k: nat)
    requires |s| > 1
    requires validRPSString(s)
    requires k > 0
    ensures simulateKRounds(s, k) == simulateKRounds(simulateRound(s), k - 1)
{
    // This follows directly from the definition of simulateKRounds
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: char)
    requires ValidInput(n, k, s)
    ensures validRPSChar(result)
// </vc-spec>
// <vc-code>
{
    var roundsLeft := k;
    var current := s;
    
    while roundsLeft > 0 && |current| > 1
        invariant 0 < |current| <= |s|
        invariant validRPSString(current)
        invariant 0 <= roundsLeft <= k
        invariant current == simulateKRounds(s, k - roundsLeft)
        decreases roundsLeft, |current|
    {
        var next := "";
        var i := 0;
        
        while i < |current| - 1
            invariant 0 <= i <= |current|
            invariant i % 2 == 0
            invariant |next| == i / 2
            invariant validRPSString(next)
            invariant forall j :: 0 <= j < |next| ==> next[j] == winner(current[2*j], current[2*j+1])
            decreases |current| - i
        {
            next := next + [winner(current[i], current[i+1])];
            i := i + 2;
        }
        
        if i < |current| {
            next := next + [current[i]];
        }
        
        assert |next| == (|current| + 1) / 2;
        assert forall j :: 0 <= j < (|current| / 2) ==> next[j] == winner(current[2*j], current[2*j+1]);
        assert |current| % 2 == 1 ==> next[|next| - 1] == current[|current| - 1];
        
        SimulateRoundEquivalence(current, next);
        assert next == simulateRound(current);
        
        var oldCurrent := current;
        var oldRoundsLeft := roundsLeft;
        
        current := next;
        roundsLeft := roundsLeft - 1;
        
        assert oldCurrent == simulateKRounds(s, k - oldRoundsLeft);
        assert current == simulateRound(oldCurrent);
        assert oldRoundsLeft > 0;
        assert |oldCurrent| > 1;
        
        SimulateKRoundsStep(simulateKRounds(s, k - oldRoundsLeft), oldRoundsLeft);
        assert simulateKRounds(simulateKRounds(s, k - oldRoundsLeft), oldRoundsLeft) == 
               simulateKRounds(simulateRound(simulateKRounds(s, k - oldRoundsLeft)), oldRoundsLeft - 1);
        assert simulateKRounds(s, k) == simulateKRounds(simulateKRounds(s, k - oldRoundsLeft), oldRoundsLeft);
        assert simulateKRounds(s, k) == simulateKRounds(oldCurrent, oldRoundsLeft);
        assert simulateKRounds(s, k) == simulateKRounds(current, roundsLeft);
        assert current == simulateKRounds(s, k - roundsLeft);
    }
    
    assert current == simulateKRounds(s, k - roundsLeft);
    
    if roundsLeft == 0 {
        assert current == simulateKRounds(s, k);
    } else {
        assert |current| == 1;
        assert simulateKRounds(current, roundsLeft) == current;
        assert current == simulateKRounds(s, k - roundsLeft);
        assert simulateKRounds(s, k) == simulateKRounds(current, roundsLeft);
        assert simulateKRounds(s, k) == current;
    }
    
    SimulateKRoundsProperties(s, k);
    assert |current| >= 1;
    
    result := current[0];
}
// </vc-code>

