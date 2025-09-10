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
                                (CanReachOne(j) ==> memo[j] == MinMovesToOne(j)) &&
                                (!CanReachOne(j) ==> memo[j] == -1) // Not strictly necessary but good for consistency
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
        else
            memo[i] := 0; // This case means 'i' is a prime factor other than 2, 3 or 5.
                          // But if CanReachOne(i) is true, 'i' must be 1.
                          // Otherwise, if CanReachOne(i) is true, then i can be reduced to 1 by
                          // successive divisions by 2, 3, or 5. This implies i must be of the form 2^a * 3^b * 5^c.
                          // So, this 'else' branch implies i has other prime factors, which contradicts CanReachOne(i).
                          // Therefore, if CanReachOne(i) is true, this branch will not be taken.
                          // Hence, we assign 0 to satisfy type correctness. The else if CanReachOne(i) condition will cover the rest.
    }
    return memo[n];
}
// </vc-code>

