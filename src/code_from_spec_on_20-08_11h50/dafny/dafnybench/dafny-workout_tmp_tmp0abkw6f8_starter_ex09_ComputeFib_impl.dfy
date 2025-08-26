// <vc-spec>
function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
        fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
lemma FibIterativeCorrectness(k: nat, a: nat, b: nat)
    requires k >= 1
    requires a == fib(k - 1)
    requires b == fib(k)
    ensures a + b == fib(k + 1)
{
    // The lemma body is empty because Dafny can prove this automatically
    // from the definition of fib and the preconditions
}
// </vc-helpers>

method ComputeFib(n: nat) returns (b: nat)
    ensures b == fib(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 1;
    } else {
        var a := 0;
        var curr := 1;
        var i := 1;
        
        while i < n
            invariant 1 <= i <= n
            invariant a == fib(i - 1)
            invariant curr == fib(i)
        {
            FibIterativeCorrectness(i, a, curr);
            var temp := a + curr;
            a := curr;
            curr := temp;
            i := i + 1;
        }
        
        return curr;
    }
}
// </vc-code>