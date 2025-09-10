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
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: char)
    requires ValidInput(n, k, s)
    ensures validRPSChar(result)
// </vc-spec>
// <vc-code>
{
    var rounds := k;
    var current := s;
    
    while rounds > 0 && |current| > 1
        invariant |current| > 0
        invariant validRPSString(current)
        invariant current == simulateKRounds(s, k - rounds)
        decreases rounds
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
        
        current := next;
        rounds := rounds - 1;
    }
    
    SimulateKRoundsProperties(s, k);
    assert current == simulateKRounds(s, k);
    assert |current| >= 1;
    
    result := current[0];
}
// </vc-code>

