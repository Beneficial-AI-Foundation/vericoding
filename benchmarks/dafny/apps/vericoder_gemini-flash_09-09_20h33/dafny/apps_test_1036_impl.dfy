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
function Fight(a: char, b: char): char
    requires validRPSChar(a) && validRPSChar(b)
    ensures validRPSChar(Fight(a,b))
{
    if (a, b) == ('R', 'S') || (a, b) == ('S', 'P') || (a, b) == ('P', 'R') then a
    else if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') then b
    else a // a == b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: char)
    requires ValidInput(n, k, s)
    ensures validRPSChar(result)
// </vc-spec>
// <vc-code>
{
    var currentRoundWinners := s; // string of n chars
    
    for round := 0 to k-1
        invariant 0 <= round <= k
        invariant |currentRoundWinners| >= 1
        invariant validRPSString(currentRoundWinners)
        invariant forall i :: 0 <= i < |currentRoundWinners| ==> validRPSChar(currentRoundWinners[i])
    {
        if |currentRoundWinners| == 1 {
            break;
        }

        var nextRoundWinners := "";
        var i := 0;
        while i + 1 < |currentRoundWinners|
            invariant 0 <= i <= |currentRoundWinners|
            invariant i % 2 == 0
            invariant validRPSString(nextRoundWinners)
            invariant forall j :: 0 <= j < |nextRoundWinners| ==> (var fightResult := Fight(currentRoundWinners[2*j], currentRoundWinners[2*j+1]); nextRoundWinners[j] == fightResult)
            invariant forall j :: 0 <= j < i ==> (validRPSChar(currentRoundWinners[j]))
            invariant (i / 2) == |nextRoundWinners|
            invariant |currentRoundWinners| >= 2
        {
            var winnerChar := Fight(currentRoundWinners[i], currentRoundWinners[i+1]);
            nextRoundWinners := nextRoundWinners + [winnerChar];
            i := i + 2;
        }

        if i < |currentRoundWinners| { 
            nextRoundWinners := nextRoundWinners + [currentRoundWinners[i]];
        }
        currentRoundWinners := nextRoundWinners;
    }
    result := currentRoundWinners[0];
}
// </vc-code>

