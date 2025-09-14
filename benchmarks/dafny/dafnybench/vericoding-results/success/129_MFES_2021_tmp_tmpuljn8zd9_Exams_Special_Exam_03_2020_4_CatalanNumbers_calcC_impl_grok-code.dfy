function C(n: nat): nat 
    decreases n
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
// </vc-spec>
// <vc-code>
decreases n
    {
        if n == 0 {
            res := 1;
        } else {
            var temp := calcC(n - 1);
            res := (4 * n - 2) * temp / (n + 1);
        }
    }
// </vc-code>

