// <vc-preamble>
// ======= TASK =======
// Compute the n-th element of the Fib4 sequence, defined as:
// fib4(0) = 0, fib4(1) = 0, fib4(2) = 2, fib4(3) = 0
// fib4(n) = fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4) for n >= 4
// The solution must be iterative and efficient.

// ======= SPEC REQUIREMENTS =======
function fib4_func(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else if n == 1 then 0
    else if n == 2 then 2
    else if n == 3 then 0
    else fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4)
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method fib4(n: int) returns (result: int)
    requires n >= 0
    ensures result == fib4_func(n)
    ensures n == 0 ==> result == 0
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 2
    ensures n == 3 ==> result == 0
    ensures n >= 4 ==> result == fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4)
// </vc-spec>
// <vc-code>
{
    // Base cases
    if n == 0 {
        result := 0;
    } else if n == 1 {
        result := 0;
    } else if n == 2 {
        result := 2;
    } else if n == 3 {
        result := 0;
    } else {
        // For n >= 4, use iterative approach
        // Keep track of the last 4 values
        var a := 0;  // fib4(0)
        var b := 0;  // fib4(1)
        var c := 2;  // fib4(2)
        var d := 0;  // fib4(3)

        // Compute fib4(4) through fib4(n)
        var i := 4;
        while i <= n
            invariant 4 <= i <= n + 1
            invariant i == 4 ==> (a == fib4_func(0) && b == fib4_func(1) && c == fib4_func(2) && d == fib4_func(3))
            invariant i > 4 ==> (a == fib4_func(i-4) && b == fib4_func(i-3) && c == fib4_func(i-2) && d == fib4_func(i-1))
        {
            var next_val := a + b + c + d;
            // Shift the window: move everything one position left
            a := b;
            b := c;
            c := d;
            d := next_val;
            i := i + 1;
        }

        result := d;
    }
}
// </vc-code>
