Given an integer a, count the number of times the digit '1' appears in its octal (base-8) representation.
Input: A single integer a where 0 ≤ a ≤ 1,000,000
Output: A single integer representing the count of digit '1' in the octal representation of a

function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

method solve(a: int) returns (count: int)
    requires a >= 0
    ensures count >= 0
    ensures count == CountOnesInOctal(a)
{
    if a == 0 {
        count := 0;
        return;
    }

    var num := a;
    count := 0;

    while num > 0
        invariant num >= 0
        invariant count >= 0
        invariant count + CountOnesInOctal(num) == CountOnesInOctal(a)
    {
        var digit := num % 8;
        if digit == 1 {
            count := count + 1;
        }
        num := num / 8;
    }
}
