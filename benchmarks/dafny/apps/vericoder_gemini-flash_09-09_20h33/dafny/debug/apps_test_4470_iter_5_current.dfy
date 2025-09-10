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
    if !CanReachOne(n)
    {
        return -1;
    }
    
    if n == 1
    {
        return 0;
    }
    
    var memo := new array<int>(n + 1, k => 0); // Initialize with dummy value 0. The first verification error was here, missing the anonymous constructor `_ => _`.
    memo[1] := 0;

    for i := 2 to n
        invariant 2 <= i <= n + 1
        invariant forall j :: 1 <= j < i ==> 
                                (CanReachOne(j) && memo[j] == MinMovesToOne(j)) ||
                                (!CanReachOne(j) && memo[j] == -1)
    {
        if !CanReachOne(i)
        {
            memo[i] := -1;
        }
        else if i % 2 == 0 && i % 3 != 0 && i % 5 != 0
        {
            memo[i] := 1 + memo[i/2];
        }
        else if i % 3 == 0 && i % 2 != 0 && i % 5 != 0
        {
            memo[i] := 2 + memo[i/3];
        }
        else if i % 5 == 0 && i % 2 != 0 && i % 3 != 0
        {
            memo[i] := 3 + memo[i/5];
        }
        else if i % 2 == 0 && i % 3 == 0 && i % 5 != 0
        {
            memo[i] := Min(1 + memo[i/2], 2 + memo[i/3]);
        }
        else if i % 2 == 0 && i % 5 == 0 && i % 3 != 0
        {
            memo[i] := Min(1 + memo[i/2], 3 + memo[i/5]);
        }
        else if i % 3 == 0 && i % 5 == 0 && i % 2 != 0
        {
            memo[i] := Min(2 + memo[i/3], 3 + memo[i/5]);
        }
        else if i % 2 == 0 && i % 3 == 0 && i % 5 == 0
        {
            memo[i] := Min3(1 + memo[i/2], 2 + memo[i/3], 3 + memo[i/5]);
        }
        else
        {
            // This `else` branch implies that `i` is not divisible by 2, 3, or 5.
            // Since `CanReachOne(i)` is true at this point (because of the initial `if !CanReachOne(i)` check),
            // it means `i` must be 1, based on the definition of `CanReachOne`.
            // However, the loop starts from `i = 2`.
            // Therefore, this `else` branch is logically unreachable.
            // Dafny requires a statement here. Assigning 0 is semantically consistent with an unreachable branch.
            memo[i] := 0; // Unreachable code, but required by Dafny for completeness.
        }
    }
    return memo[n];
}
// </vc-code>

