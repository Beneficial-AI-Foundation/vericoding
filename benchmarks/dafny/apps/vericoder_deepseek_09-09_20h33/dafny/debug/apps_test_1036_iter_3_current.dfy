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

function winnerN(round: string, k: int): char
    requires |round| == pow2(k) && validRPSString(round)
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
    requires |r1| == |r2| == pow2(k) && validRPSString(r1) && validRPSString(r2)
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
    requires |s| == pow2(k) && validRPSString(s)
    ensures winnerN(s, k) == winnerN(s + s, k)
{
    WinnersAgree(s, s + s, k);
}

function pow2(k: int): int
    requires k >= 0
    decreases k
{
    if k == 0 then 1 else 2 * pow2(k-1)
}

function Log2(n: int): int
    requires n > 0 && (exists k :: n == pow2(k))
    ensures pow2(result) == n
{
    if n == 1 then 0 else Log2(n/2) + 1
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
        invariant 1 <= powerOfTwo <= pow2(k)
        invariant cycles >= 0 && cycles + Log2(powerOfTwo) == k
    {
        powerOfTwo := powerOfTwo * 2;
        cycles := cycles - 1;
    }
    
    var extendedString := s;
    var i := 0;
    while i < powerOfTwo - n
        invariant 0 <= i <= powerOfTwo - n
        invariant |extendedString| == n + i
        invariant extendedString[0..n] == s
        invariant forall j :: 0 <= j < i ==> extendedString[n+j] == s[j % n]
    {
        extendedString := extendedString + [s[i % n]];
        i := i + 1;
    }
    
    result := winnerN(extendedString[0..powerOfTwo], k);
}
// </vc-code>

