method IsPerfectSquare(n: int) returns (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
    ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        result := true;
        assert 0 <= 0 <= n && 0 * 0 == n;
        return;
    }
    
    var i := 0;
    while i * i < n
        invariant i >= 0
        invariant i * i <= n
        invariant forall j: int :: 0 <= j < i ==> j * j < n
    {
        i := i + 1;
        assert i >= 1;
        if i * i > n {
            assert forall j: int :: 0 <= j < i ==> j * j < n;
            assert (i-1) * (i-1) < n < i * i;
            result := false;
            return;
        }
    }
    
    if i * i == n {
        result := true;
        assert 0 <= i <= n && i * i == n;
    } else {
        result := false;
        assert i * i > n;
        assert forall j: int :: 0 <= j < i ==> j * j < n;
    }
}
// </vc-code>
// <vc-helpers>
// </vc-helpers>