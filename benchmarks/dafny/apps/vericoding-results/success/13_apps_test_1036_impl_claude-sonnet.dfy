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
lemma WinnerIsValid(a: char, b: char)
    requires validRPSChar(a) && validRPSChar(b)
    ensures validRPSChar(winner(a, b))
{
}

lemma SimulateRoundPreservesValidity(s: string)
    requires |s| > 0 && validRPSString(s)
    ensures var newS := if |s| == 1 then s else seq(|s| - 1, i requires 0 <= i < |s| - 1 => winner(s[i], s[i + 1]));
            validRPSString(newS)
{
    if |s| > 1 {
        var newS := seq(|s| - 1, i requires 0 <= i < |s| - 1 => winner(s[i], s[i + 1]));
        forall i | 0 <= i < |newS|
            ensures validRPSChar(newS[i])
        {
            WinnerIsValid(s[i], s[i + 1]);
        }
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
    var current := s;
    var rounds := k;
    
    while rounds > 0 && |current| > 1
        invariant validRPSString(current)
        invariant |current| > 0
        decreases rounds, |current|
    {
        SimulateRoundPreservesValidity(current);
        var next := seq(|current| - 1, i requires 0 <= i < |current| - 1 => winner(current[i], current[i + 1]));
        current := next;
        rounds := rounds - 1;
    }
    
    result := current[0];
}
// </vc-code>

