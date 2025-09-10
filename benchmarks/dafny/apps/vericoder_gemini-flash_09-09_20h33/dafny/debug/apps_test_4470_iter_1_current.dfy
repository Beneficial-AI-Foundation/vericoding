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
function method Min(a: nat, b: nat): nat
  reads {}
{
  if a < b then a else b
}
function method Min3(a: nat, b: nat, c: nat): nat
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
            memo[i] := -1; // Should not happen if CanReachOne(i) is true for the current i and its divisors.
    }
    return memo[n];
}
// </vc-code>

