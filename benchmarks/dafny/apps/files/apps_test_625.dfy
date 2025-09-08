Given a positive integer n, calculate the value of the alternating sum:
f(n) = -1 + 2 - 3 + 4 - 5 + ... + (-1)^n × n

function AlternatingSum(n: int): int
    requires n > 0
{
    if n == 1 then -1
    else AlternatingSum(n-1) + (if n % 2 == 0 then n else -n)
}

predicate ValidInput(n: int) {
    n > 0
}

lemma AlternatingSumEquivalence(n: int)
    requires n > 0
    ensures n % 2 == 0 ==> AlternatingSum(n) == n / 2
    ensures n % 2 != 0 ==> AlternatingSum(n) == n / 2 - n
{
    if n == 1 {
        // Base case: AlternatingSum(1) = -1, and 1/2 - 1 = 0 - 1 = -1
    } else {
        AlternatingSumEquivalence(n-1);
        if n % 2 == 0 {
            // n is even, so n-1 is odd
            // AlternatingSum(n) = AlternatingSum(n-1) + n
            // AlternatingSum(n) = ((n-1)/2 - (n-1)) + n
            // AlternatingSum(n) = (n-1)/2 - n + 1 + n = (n-1)/2 + 1 = n/2
        } else {
            // n is odd, so n-1 is even  
            // AlternatingSum(n) = AlternatingSum(n-1) - n
            // AlternatingSum(n) = (n-1)/2 - n = n/2 - n (since (n-1)/2 = n/2 for odd n)
        }
    }
}

method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == AlternatingSum(n)
    ensures n % 2 == 0 ==> result == n / 2
    ensures n % 2 != 0 ==> result == n / 2 - n
{
    AlternatingSumEquivalence(n);
    var x := n / 2;
    if n % 2 == 0 {
        result := x;
    } else {
        result := x - n;
    }
}
