// <vc-preamble>
function SumOfDigits(x: nat): nat
    decreases x
{
    if x == 0 then 0 else (x % 10) + SumOfDigits(x / 10)
}

predicate IsSumDivisibleBy(x: nat, d: nat)
    requires d > 0
{
    (SumOfDigits(x) % d) == 0
}
// </vc-preamble>

// <vc-helpers>
function CountUpTo(k: nat, d: nat): nat
    requires d > 0
    decreases k
{
    if k == 0 then 0
    else CountUpTo(k - 1, d) + (if IsSumDivisibleBy(k, d) then 1 else 0)
}

lemma CountUpTo_is_bounded(k: nat, d: nat)
    requires d > 0
    ensures CountUpTo(k, d) <= k
    decreases k
{
    if k > 0 {
        CountUpTo_is_bounded(k - 1, d);
    }
}
// </vc-helpers>

// <vc-spec>
method CountSumDivisibleBy(n: nat, d: nat) returns (result: nat)
    requires d > 0
    ensures result <= n
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 1;
    while i <= n
        invariant d > 0
        invariant 1 <= i <= n + 1
        invariant result == CountUpTo(i - 1, d)
    {
        if IsSumDivisibleBy(i, d) {
            result := result + 1;
        }
        i := i + 1;
    }
    CountUpTo_is_bounded(n, d);
}
// </vc-code>
