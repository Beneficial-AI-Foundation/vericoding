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
lemma MinMovesToOneDecreases(n: nat)
    requires n > 0 && CanReachOne(n)
    ensures n == 1 || n % 2 == 0 || n % 3 == 0 || n % 5 == 0
    decreases n
{
    if n == 1 {
        return;
    }
    if n % 2 == 0 {
        assert n / 2 < n;
    } else if n % 3 == 0 {
        assert n / 3 < n;
    } else if n % 5 == 0 {
        assert n / 5 < n;
    } else {
        assert !OnlyFactors235(n);
        assert false;
    }
}

lemma MinMovesToOnePositive(n: nat)
    requires n > 0 && CanReachOne(n)
    ensures MinMovesToOne(n) >= 0
    decreases n
{
    if n == 1 {
    } else if n % 2 == 0 {
        MinMovesToOnePositive(n / 2);
    } else if n % 3 == 0 {
        MinMovesToOnePositive(n / 3);
    } else if n % 5 == 0 {
        MinMovesToOnePositive(n / 5);
    }
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
    if !CanReachOne(n) {
        result := -1;
    } else {
        var moves := 0;
        var current := n;
        
        while current != 1
            invariant current > 0
            invariant CanReachOne(current)
            invariant moves + MinMovesToOne(current) == MinMovesToOne(n)
            decreases current
        {
            MinMovesToOneDecreases(current);
            if current % 2 == 0 {
                current := current / 2;
                moves := moves + 1;
            } else if current % 3 == 0 {
                current := current / 3;
                moves := moves + 2;
            } else if current % 5 == 0 {
                current := current / 5;
                moves := moves + 3;
            }
        }
        
        result := moves;
    }
}
// </vc-code>

