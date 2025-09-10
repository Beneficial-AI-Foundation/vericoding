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
function isLimitedPrimeHelper(p: int, divisor: int): bool
requires p >= 1
requires divisor >= 1
requires divisor % 2 != 0
// We need to ensure that divisor * divisor does not overflow, so we add a check.
// Also, the upper bound for divisor*divisor can be p, so we avoid adding +2.
requires divisor * divisor <= p + divisor // ensures the recursion terminates and handles the base case correctly in relation to multiplication
ensures isLimitedPrimeHelper(p, divisor) ==> (forall k :: divisor <= k && k * k <= p && p % k == 0 ==> false)
ensures !isLimitedPrimeHelper(p, divisor) <==> (exists k :: divisor <= k && k * k <= p && p % k == 0)
{
    if divisor * divisor > p then
        true // p is prime, as no divisors found up to sqrt(p)
    else if p % divisor == 0 then
        false // p has a divisor, so not prime
    else
        isLimitedPrimeHelper(p, divisor + 2)
}
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
    var numCases := input[0];
    var results := new string[numCases];

    for i := 0 to numCases - 1
        invariant 0 <= i <= numCases
        invariant forall j :: 0 <= j < i ==> results[j] == determineWinner(input[j+1])
    {
        var n := input[i+1];
        results[i] := determineWinner(n);
    }
    return results[..];
}
// </vc-code>

