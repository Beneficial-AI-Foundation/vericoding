function Power(n:nat):nat 
{
    if n == 0 then 1 else 2 * Power(n-1)
}

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma PowerUnfold(n: nat)
    ensures n > 0 ==> Power(n) == 2 * Power(n-1)
{
    if n > 0 {
        assert Power(n) == 2 * Power(n-1);
    }
}

lemma PowerIterative(i: nat, acc: nat)
    requires acc == Power(i)
    ensures acc * Power(0) == Power(i)
{
    assert Power(0) == 1;
    assert acc * 1 == acc;
}

lemma PowerCorrectness(n: nat, i: nat, acc: nat)
    requires i <= n
    requires acc == Power(i)
    ensures acc == Power(i)
    decreases n - i
{
    // Base case - this lemma just establishes the loop invariant
}
// </vc-helpers>

// <vc-spec>
method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        p := 1;
    } else {
        var i := 0;
        p := 1;
        
        while i < n
            invariant 0 <= i <= n
            invariant p == Power(i)
        {
            PowerUnfold(i + 1);
            p := 2 * p;
            i := i + 1;
        }
    }
}
// </vc-code>

