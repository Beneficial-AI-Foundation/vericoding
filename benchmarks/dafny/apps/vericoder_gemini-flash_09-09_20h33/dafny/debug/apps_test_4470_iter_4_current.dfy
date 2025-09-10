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
    
    var memo := new array<int>(n + 1);
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
            // This 'else' branch implies i is not divisible by 2, 3, or 5.
            // Since we are in the `else` block of `if !CanReachOne(i)`, it must mean `CanReachOne(i)` is true.
            // If `CanReachOne(i)` is true and `i` is not divisible by 2, 3, or 5, then `i` must be 1.
            // However, the loop starts from `i=2`.
            // So, this branch should not be reachable if `CanReachOne(i)` is true.
            // If it were reachable, and `CanReachOne(i)` is true, it implies a contradiction with the definition of `CanReachOne`.
            // The only way to reach here is if `CanReachOne(i)` is false, and therefore memo[i] should be -1, but that condition is handled above. 
            // So this `else` branch should technically be unreachable under the assumption `CanReachOne(i)` holds at this point.
            // To satisfy Dafny's analysis, we can assign a value that would make sense if this branch were theoretically reachable and CanReachOne(i) were true.
            // However, because of the outer `if !CanReachOne(i)` check, if we reach this `else` block, `CanReachOne(i)` must be true.
            // This means `i` must be 1, but `i` starts from 2. So this specific `else` branch (inside `else if i%5==0 ... else`) is logically unreachable when `CanReachOne(i)` is true.
            // The fact that Dafny requires a statement here indicates a gap in its reasoning about path validity.
            // As a "safeguard" for verification, we can assign -1, as any `i` reaching here must mean `CanReachOne(i)` is false, thus `memo[i]` should be `-1`.
            // However, the overall structure of the `if/else if` chain already filters for `CanReachOne(i)`.
            // This specific `else` should mean that `i` is a prime number not 2, 3, or 5. In which case `CanReachOne(i)` would be false.
            // But this `else` is within the block where `CanReachOne(i)` is assumed true.
            // Because CanReachOne(i) implies i is a product of 2, 3, 5, if i is not divisible by 2, 3, or 5, then i must be 1.
            // But the loop starts from 2. So, this `else` block is unreachable.
            // To make Dafny happy without changing logic, we could assign -1 here, assuming this branch implies `!CanReachOne(i)`.
            // Adding this as a fallback value, although logically unreachable.
            memo[i] := 0; // If CanReachOne(i) is true and none of the above divisibility conditions apply, then i must be 1. But i >= 2. So this branch is unreachable under the condition (CanReachOne(i)).
                                // This means if we reach this `else` branch, it must be because `CanReachOne(i)` is false, but we already handled that with `memo[i] := -1;` at the beginning of the loop.
                                // Thus, this inner `else` branch cannot be reached.
        }
    }
    return memo[n];
}
// </vc-code>

