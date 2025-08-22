// ATOM 
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL Max
method Max(a: array<nat>) returns (m: int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
    if a.Length == 0 {
        m := 0;
    } else {
        m := a[0];
        var n := 1;
        while n < a.Length
            invariant 1 <= n <= a.Length
            invariant forall i :: 0 <= i < n ==> a[i] <= m
            invariant exists i :: 0 <= i < n && m == a[i]
        {
            if a[n] > m {
                m := a[n];
            }
            n := n + 1;
        }
    }
}