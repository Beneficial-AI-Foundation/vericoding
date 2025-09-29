

// <vc-helpers>
lemma SquareMonotonic(a: int, b: int)
    requires 0 <= a < b
    ensures a * a < b * b
{
    // Since 0 <= a < b, we have a * a <= a * b - a (because a * (b - 1) >= 0)
    // And a * b < b * b (because a < b implies a * b < b * b)
    assert a >= 0;
    assert b > a;
    assert a * a <= a * b;
    assert a * b < b * b;
}

lemma SquareBounds(n: int, i: int)
    requires n >= 0
    requires 0 <= i
    requires i * i <= n < (i + 1) * (i + 1)
    ensures forall a: int :: 0 < a * a < n ==> a < i + 1
{
    forall a: int | 0 < a * a < n
    ensures a < i + 1
    {
        if a >= i + 1 {
            assert a * a >= (i + 1) * (i + 1);
            assert (i + 1) * (i + 1) > n;
            assert a * a > n;
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method IsPerfectSquare(n: int) returns (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
    ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        assert 0 * 0 == 0;
        assert 0 * 0 == n;
        return true;
    }
    
    var i := 0;
    while i * i < n
        invariant 0 <= i
        invariant forall j: int :: 0 <= j < i ==> j * j < n
    {
        i := i + 1;
    }
    
    if i * i == n {
        assert i * i == n;
        result := true;
    } else {
        assert i * i > n;
        assert i > 0;
        assert (i - 1) * (i - 1) < n;
        assert (i - 1) * (i - 1) < n < i * i;
        SquareBounds(n, i - 1);
        assert forall a: int :: 0 < a * a < n ==> a < i;
        assert forall a: int :: 0 < a * a < n ==> a * a != n;
        result := false;
    }
}
// </vc-code>

