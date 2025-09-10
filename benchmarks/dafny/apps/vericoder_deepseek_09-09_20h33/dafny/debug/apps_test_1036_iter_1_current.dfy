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
function winnerN(round: string, k: int): char
    requires |round| == (1 << k) && validRPSString(round)
    ensures validRPSChar(winnerN(round, k))
{
    if k == 0 then
        round[0]
    else
        var left := winnerN(round[0..|round|/2], k-1);
        var right := winnerN(round[|round|/2..], k-1);
        winner(left, right)
}

lemma WinnersAgree(r1: string, r2: string, k: int)
    requires |r1| == |r2| == (1 << k) && validRPSString(r1) && validRPSString(r2)
    requires forall i :: 0 <= i < |r1| ==> r1[i] == r2[i] || (|r1| == 1 && i == 0)
    ensures winnerN(r1, k) == winnerN(r2, k)
{
    if k > 0 {
        var mid := |r1|/2;
        WinnersAgree(r1[0..mid], r2[0..mid], k-1);
        WinnersAgree(r1[mid..], r2[mid..], k-1);
    }
}

lemma CyclicWinner(s: string, k: int)
    requires |s| == (1 << k) && validRPSString(s)
    ensures winnerN(s, k) == winnerN(s + s, k)
{
    WinnersAgree(s, s + s, k);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: char)
    requires ValidInput(n, k, s)
    ensures validRPSChar(result)
// </vc-spec>
// <vc-code>
{
    if k == 0 {
        result := s[0];
        return;
    }
    
    var powerOfTwo := 1;
    var cycles := k;
    while cycles > 0
        invariant 1 <= powerOfTwo <= (1 << k)
        invariant cycles >= 0 && cycles + (if powerOfTwo == 1 then 0 else var log := 0; while powerOfTwo != (1 << log) { log := log + 1 } log) == k
    {
        powerOfTwo := powerOfTwo * 2;
        cycles := cycles - 1;
    }
    
    var index := 0;
    result := s[0];
    var i := 0;
    while i < powerOfTwo
        invariant 0 <= i <= powerOfTwo
        invariant index == 0
        invariant result == s[0]
    {
        var next := (index + 1) % n;
        result := winner(result, s[next]);
        index := next;
        i := i + 1;
    }
    
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result == winnerN(s[0..powerOfTwo], k)  // Use appropriate k for the current powerOfTwo
    {
        // This invariant would need more careful setup
        i := i + 1;
    }
    
    result := winnerN(s[0..powerOfTwo], k);
}
// </vc-code>

