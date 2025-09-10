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
lemma ReduceByFactors235Properties(n: nat)
    requires n > 0
    ensures ReduceByFactors235(n) == 1 ==> CanReachOne(n)
    ensures ReduceByFactors235(n) != 1 ==> !CanReachOne(n)
{
    // This follows directly from the definitions
}

lemma MinMovesCorrect(n: nat)
    requires n > 0
    requires CanReachOne(n)
    ensures MinMovesToOne(n) >= 0
{
    // This follows from the definition of MinMovesToOne
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
    var reduced := ReduceByFactors235(n);
    
    if reduced == 1 {
        // n can reach 1, so calculate the minimum moves
        result := MinMovesToOne(n);
        assert CanReachOne(n) by {
            assert OnlyFactors235(n);
        }
    } else {
        // n cannot reach 1
        result := -1;
        assert !CanReachOne(n) by {
            assert !OnlyFactors235(n);
            assert ReduceByFactors235(n) != 1;
        }
    }
}
// </vc-code>

