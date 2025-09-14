

// <vc-helpers>
lemma SquareMonotonic(a: int, b: int)
    requires 0 <= a <= b
    ensures a * a <= b * b
{
}

lemma SquareGrowth(i: int)
    requires i >= 0
    ensures i * i >= i
{
}

lemma SquareBounds(i: int, n: int)
    requires i > 0 && i * i > n
    ensures forall j: int :: j > i ==> j * j > n
{
}

lemma ExistsWitness(i: int, n: int)
    requires 0 <= i <= n && i * i == n
    ensures exists j: int :: 0 <= j <= n && j * j == n
{
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
        assert 0 <= 0 <= n && 0 * 0 == n;
        return true;
    }
    
    var i := 0;
    while i <= n && i * i <= n
        invariant 0 <= i <= n + 1
        invariant forall j: int :: 0 <= j < i ==> j * j != n
        invariant i <= n + 1
        decreases n - i * i + 1
    {
        if i * i == n {
            assert 0 <= i <= n && i * i == n;
            ExistsWitness(i, n);
            return true;
        }
        i := i + 1;
    }
    
    return false;
}
// </vc-code>

