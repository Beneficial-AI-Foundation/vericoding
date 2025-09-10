predicate ValidInput(n: nat)
{
    n > 0
}

predicate CanReachOne(n: nat)
    requires n > 0
{
    OnlyFactors235(n)
}

predicate OnlyFactors235(n: nat)
    requires n > 0
{
    ReduceByFactors235(n) == 1
}

function ReduceByFactors235(n: nat): nat
    requires n > 0
    decreases n
{
    if n == 1 then 1
    else if n % 2 == 0 then ReduceByFactors235(n / 2)
    else if n % 3 == 0 then ReduceByFactors235(n / 3)
    else if n % 5 == 0 then ReduceByFactors235(n / 5)
    else n
}

function MinMovesToOne(n: nat): nat
    requires n > 0
    requires CanReachOne(n)
    decreases n
{
    if n == 1 then 0
    else if n % 2 == 0 then 1 + MinMovesToOne(n / 2)
    else if n % 3 == 0 then 2 + MinMovesToOne(n / 3)
    else if n % 5 == 0 then 3 + MinMovesToOne(n / 5)
    else 0
}

// <vc-helpers>
function Min(a: nat, b: nat): nat
  reads {}
{
  if a < b then a else b
}
function Min3(a: nat, b: nat, c: nat): nat
  reads {}
{
  Min(a, Min(b,c))
}
// </vc-helpers>

// <vc-spec>
method Solve(n: nat) returns (result: int)
    requires ValidInput(n)
    ensures result >= -1
    ensures result == -1 <==> !CanReachOne(n)
    ensures result >= 0 ==> CanReachOne(n) && result == MinMovesToOne(n)
// </vc-spec>
// <vc-code>
{
    if !CanReachOne(n) then
        return -1;
    
    if n == 1 then
        return 0;
    
    var memo := new array<int>(n + 1);
    memo[1] := 0;

    for i := 2 to n
        invariant 2 <= i <= n + 1
        invariant forall j :: 1 <= j < i ==> 
                                (CanReachOne(j) && memo[j] == MinMovesToOne(j)) ||
                                (!CanReachOne(j) && memo[j] == -1) // Corrected from `|| (!CanReachOne(j) ==> memo[j] == -1)`
    {
        if !CanReachOne(i) then
            memo[i] := -1;
        else if i % 2 == 0 && i % 3 != 0 && i % 5 != 0 then
            memo[i] := 1 + memo[i/2];
        else if i % 3 == 0 && i % 2 != 0 && i % 5 != 0 then
            memo[i] := 2 + memo[i/3];
        else if i % 5 == 0 && i % 2 != 0 && i % 3 != 0 then
            memo[i] := 3 + memo[i/5];
        else if i % 2 == 0 && i % 3 == 0 && i % 5 != 0 then
            memo[i] := Min(1 + memo[i/2], 2 + memo[i/3]);
        else if i % 2 == 0 && i % 5 == 0 && i % 3 != 0 then
            memo[i] := Min(1 + memo[i/2], 3 + memo[i/5]);
        else if i % 3 == 0 && i % 5 == 0 && i % 2 != 0 then
            memo[i] := Min(2 + memo[i/3], 3 + memo[i/5]);
        else if i % 2 == 0 && i % 3 == 0 && i % 5 == 0 then
            memo[i] := Min3(1 + memo[i/2], 2 + memo[i/3], 3 + memo[i/5]);
        else // This implies i is only divisible by 1 (i.e. it is prime, and not 2, 3, or 5)
             // or it has prime factors other than 2, 3, 5.
             // If CanReachOne(i) is true, then 'i' must be 1. But `i` starts from 2.
             // So if `CanReachOne(i)` is true, then `i` must be of the form 2^a * 3^b * 5^c.
             // This `else` case means `i` is not divisible by 2, 3, or 5.
             // This implies that ReduceByFactors235(i) == i unless i=1.
             // So if CanReachOne(i) is true, then i must be 1.
             // But we are in a loop starting from i=2.
             // So this 'else' branch within the 'if CanReachOne(i)' block means that CanReachOne(i) must be false.
             // This is a contradiction, so this path should not be reachable if CanReachOne(i) is true.
             // The only case not covered by the above is when i is 1, in which case memo[1] is 0.
             // But the loop starts from i=2.
            memo[i] := 0; // This specific assignment `0` is unreachable given the `CanReachOne(i)` initial check.
    }
    return memo[n];
}
// </vc-code>

