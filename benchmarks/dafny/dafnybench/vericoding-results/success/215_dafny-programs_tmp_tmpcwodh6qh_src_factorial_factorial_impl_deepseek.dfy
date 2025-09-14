function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

// <vc-helpers>
lemma fact_pos(n: nat)
    ensures fact(n) >= 1
{
    if n == 0 {
    } else {
        fact_pos(n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        res := 1;
    } else {
        var r : nat;
        r := factorial(n - 1);
        res := n * r;
    }
}
// </vc-code>

