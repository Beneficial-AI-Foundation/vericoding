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
lemma ReducePreservesReachability(n: nat)
    requires n > 0
    ensures n % 2 == 0 ==> (CanReachOne(n) <==> CanReachOne(n / 2))
    ensures n % 3 == 0 ==> (CanReachOne(n) <==> CanReachOne(n / 3))
    ensures n % 5 == 0 ==> (CanReachOne(n) <==> CanReachOne(n / 5))
{
    if n % 2 == 0 {
        assert ReduceByFactors235(n) == ReduceByFactors235(n / 2);
    }
    if n % 3 == 0 {
        assert ReduceByFactors235(n) == ReduceByFactors235(n / 3);
    }
    if n % 5 == 0 {
        assert ReduceByFactors235(n) == ReduceByFactors235(n / 5);
    }
}

function ComputeMinMoves(n: nat): nat
    requires n > 0
    decreases n
{
    if n == 1 then 0
    else if n % 2 == 0 then 1 + ComputeMinMoves(n / 2)
    else if n % 3 == 0 then 2 + ComputeMinMoves(n / 3)
    else if n % 5 == 0 then 3 + ComputeMinMoves(n / 5)
    else 0
}

lemma ComputeMinMovesCorrect(n: nat)
    requires n > 0
    requires CanReachOne(n)
    ensures ComputeMinMoves(n) == MinMovesToOne(n)
    decreases n
{
    if n == 1 {
        assert ComputeMinMoves(n) == 0 == MinMovesToOne(n);
    } else if n % 2 == 0 {
        ReducePreservesReachability(n);
        ComputeMinMovesCorrect(n / 2);
        assert ComputeMinMoves(n) == 1 + ComputeMinMoves(n / 2) == 1 + MinMovesToOne(n / 2) == MinMovesToOne(n);
    } else if n % 3 == 0 {
        ReducePreservesReachability(n);
        ComputeMinMovesCorrect(n / 3);
        assert ComputeMinMoves(n) == 2 + ComputeMinMoves(n / 3) == 2 + MinMovesToOne(n / 3) == MinMovesToOne(n);
    } else if n % 5 == 0 {
        ReducePreservesReachability(n);
        ComputeMinMovesCorrect(n / 5);
        assert ComputeMinMoves(n) == 3 + ComputeMinMoves(n / 5) == 3 + MinMovesToOne(n / 5) == MinMovesToOne(n);
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
    var reduced := ReduceByFactors235(n);
    if reduced == 1 {
        var moves := ComputeMinMoves(n);
        ComputeMinMovesCorrect(n);
        result := moves;
    } else {
        result := -1;
    }
}
// </vc-code>

