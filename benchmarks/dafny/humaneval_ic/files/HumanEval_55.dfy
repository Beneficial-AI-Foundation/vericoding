This task involves computing the n-th Fibonacci number using 1-based indexing, where fib(1) = 1 and fib(2) = 1. The implementation should efficiently calculate the result for positive integers n.

The solution uses an iterative approach with loop invariants to maintain correctness while avoiding the exponential time complexity of a naive recursive implementation.

// ======= TASK =======
// Compute the n-th Fibonacci number using 1-based indexing, where fib(1) = 1, fib(2) = 1.
// Input: A positive integer n. Output: The n-th Fibonacci number.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int) {
    n > 0
}

function fib_spec(n: int): int
    requires n > 0
{
    if n == 1 then 1
    else if n == 2 then 1
    else fib_spec(n-1) + fib_spec(n-2)
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method fib(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == fib_spec(n)
    ensures result > 0
{
    if n == 1 || n == 2 {
        return 1;
    }

    var a := 1;
    var b := 1;
    var i := 3;

    while i <= n
        decreases n - i
        invariant i >= 3 && i <= n + 1
        invariant a == fib_spec(i-2)
        invariant b == fib_spec(i-1)
    {
        var temp := a + b;
        a := b;
        b := temp;
        i := i + 1;
    }

    return b;
}
