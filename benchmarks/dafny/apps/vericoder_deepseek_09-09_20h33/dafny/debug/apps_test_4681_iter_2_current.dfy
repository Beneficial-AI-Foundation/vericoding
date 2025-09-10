function Lucas(n: int): int
    requires n >= 0
{
    if n == 0 then 2
    else if n == 1 then 1
    else Lucas(n-1) + Lucas(n-2)
}

predicate ValidInput(n: int) {
    1 <= n <= 86
}

// <vc-helpers>
lemma LucasLemma(n: int)
    requires n >= 2
    ensures Lucas(n) == Lucas(n-1) + Lucas(n-2)
{
    // This is just a helper lemma to make Dafny aware of the recursive definition
}

lemma LucasBounds(n: int)
    requires 0 <= n <= 86
    ensures 0 <= Lucas(n) < 9223372036854775807  // Max int value
    decreases n
{
    if n < 2 {
        // Base cases: Lucas(0) = 2, Lucas(1) = 1
    } else {
        LucasBounds(n-1);
        LucasBounds(n-2);
        LucasLemma(n);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        result := 2;
    } else if n == 1 {
        result := 1;
    } else {
        var a := 2;  // Lucas(0)
        var b := 1;  // Lucas(1)
        var temp := 0;
        var count := 2;
        
        while count <= n
            invariant 2 <= count <= n + 1
            invariant a == Lucas(count - 2)
            invariant b == Lucas(count - 1)
            decreases n - count
        {
            temp := a + b;
            a := b;
            b := temp;
            count := count + 1;
        }
        
        result := b;
    }
}
// </vc-code>

