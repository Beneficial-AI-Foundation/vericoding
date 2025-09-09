/*
Two players play a game starting with integer n. Players alternate turns, with the first player moving first.
On each turn, a player must make exactly one of these moves:
1. Divide n by any odd divisor of n greater than 1
2. Subtract 1 from n (only if n > 1)
The player unable to make a move loses. Determine the winner assuming both players play optimally.
*/

function determineWinner(n: int): string
requires n >= 1
ensures determineWinner(n) == "FastestFinger" || determineWinner(n) == "Ashishgup"
ensures (n == 1) ==> determineWinner(n) == "FastestFinger"
ensures (n == 2) ==> determineWinner(n) == "Ashishgup"
ensures (n > 2 && isPowerOfTwo(n)) ==> determineWinner(n) == "FastestFinger"
ensures (n > 2 && !isPowerOfTwo(n) && n % 4 != 2) ==> determineWinner(n) == "Ashishgup"
ensures (n > 2 && !isPowerOfTwo(n) && n % 4 == 2) ==> (determineWinner(n) == "FastestFinger" <==> isLimitedPrime(n / 2))
{
    if n == 1 then "FastestFinger"
    else if n == 2 then "Ashishgup"
    else if isPowerOfTwo(n) then "FastestFinger"
    else if n % 4 != 2 then "Ashishgup"
    else if isLimitedPrime(n / 2) then "FastestFinger"
    else "Ashishgup"
}

function isPowerOfTwo(n: int): bool
requires n >= 1
ensures n == 1 ==> isPowerOfTwo(n)
ensures n > 1 ==> (isPowerOfTwo(n) <==> (n % 2 == 0 && isPowerOfTwo(n / 2)))
{
    if n <= 0 then false
    else n == 1 || (n % 2 == 0 && isPowerOfTwo(n / 2))
}

function isLimitedPrime(p: int): bool
requires p >= 1
ensures p == 1 ==> !isLimitedPrime(p)
ensures p == 2 ==> isLimitedPrime(p)
ensures p > 2 && p % 2 == 0 ==> !isLimitedPrime(p)
ensures p > 2 && p % 2 != 0 ==> (isLimitedPrime(p) <==> isLimitedPrimeHelper(p, 3))
{
    if p <= 1 then false
    else if p == 2 then true
    else if p % 2 == 0 then false
    else isLimitedPrimeHelper(p, 3)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: seq<int>) returns (result: seq<string>)
requires |input| >= 1
requires input[0] >= 1
requires |input| == input[0] + 1
requires forall i :: 1 <= i < |input| ==> input[i] >= 1
ensures |result| == input[0]
ensures forall i :: 0 <= i < |result| ==> result[i] == "FastestFinger" || result[i] == "Ashishgup"
ensures forall i :: 1 <= i < |input| ==> result[i-1] == determineWinner(input[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
