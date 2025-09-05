Compute the special factorial of a positive integer n, defined as the product of all factorials from 1! to n!: special_factorial(n) = n! × (n-1)! × (n-2)! × ... × 1!. The implementation should use an iterative approach with proper loop invariants to ensure correctness.

// ======= TASK =======
// Compute the special factorial of a positive integer n, defined as the product of all factorials from 1! to n!:
// special_factorial(n) = n! × (n-1)! × (n-2)! × ... × 1!

// ======= SPEC REQUIREMENTS =======
function factorial_func(num: int): int
    requires num >= 0
{
    if num <= 1 then 1 else num * factorial_func(num - 1)
}

function special_factorial_func(n: int): int
    requires n >= 0
{
    if n <= 0 then 1
    else special_factorial_func(n - 1) * factorial_func(n)
}

// ======= HELPERS =======
method factorial(num: int) returns (result: int)
    requires num >= 0
    ensures result == factorial_func(num)
    ensures result > 0
{
    if num <= 1 {
        return 1;
    }
    result := 1;
    var i := 2;
    while i <= num
        invariant 2 <= i <= num + 1
        invariant result == factorial_func(i - 1)
        invariant result > 0
    {
        result := result * i;
        i := i + 1;
    }
}

// ======= MAIN METHOD =======
method special_factorial(n: int) returns (result: int)
    requires n >= 0
    ensures result == special_factorial_func(n)
    ensures result > 0
{
    if n <= 0 {
        return 1;
    }

    result := 1;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant result == special_factorial_func(i - 1)
        invariant result > 0
    {
        var fact := factorial(i);
        result := result * fact;
        i := i + 1;
    }
}
