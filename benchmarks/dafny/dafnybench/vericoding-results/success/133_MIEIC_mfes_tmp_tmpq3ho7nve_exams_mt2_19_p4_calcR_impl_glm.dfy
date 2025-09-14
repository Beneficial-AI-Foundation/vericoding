function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    var a := new nat[n+1];
    a[0] := 0;
    for i := 1 to n+1
        invariant forall j :: 0 <= j < i ==> a[j] == R(j)
    {
        var prev := a[i-1];
        if prev > i {
            a[i] := prev - i;
        } else {
            a[i] := prev + i;
        }
    }
    return a[n];
}
// </vc-code>

