predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}

// <vc-helpers>
function gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases b
{
    if b == 0 then a
    else gcd(b, a % b)
}

predicate coprime(a: int, b: int)
    requires a >= 0 && b >= 0
{
    gcd(a, b) == 1
}

predicate NoDivisor(i: int, n: int)
    requires i >= 1 && n >= 1
{
    forall j :: 2 <= j <= i ==> !(n % j == 0 && i % j == 0)
}

lemma GcdPositive(a: int, b: int)
    requires a >= 0 && b >= 0
    requires a > 0 || b > 0
    ensures gcd(a, b) > 0
    decreases b
{
    if b == 0 {
        assert gcd(a, b) == a;
        assert a > 0;
    } else {
        assert b > 0;
        GcdPositive(b, a % b);
    }
}

lemma GcdDivides(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures a > 0 ==> a % gcd(a, b) == 0
    ensures b > 0 ==> b % gcd(a, b) == 0
    decreases b
{
    if b == 0 {
        if a > 0 {
            assert gcd(a, b) == a;
            assert a % a == 0;
        }
    } else {
        var g := gcd(a, b);
        assert g == gcd(b, a % b);
        GcdDivides(b, a % b);
        
        if b > 0 {
            assert b % g == 0;
        }
        if a > 0 {
            var r := a % b;
            assert r % g == 0;
            assert b % g == 0;
            assert a == (a / b) * b + r;
            assert a % g == 0;
        }
    }
}

lemma GcdIsGreatestCommonDivisor(a: int, b: int, d: int)
    requires a >= 1 && b >= 1 && d >= 2
    requires a % d == 0 && b % d == 0
    ensures gcd(a, b) >= d
    decreases b
{
    if b == 0 {
        assert gcd(a, b) == a;
        assert a >= d;
    } else {
        var r := a % b;
        assert a == (a / b) * b + r;
        assert r % d == 0;
        if r > 0 {
            GcdIsGreatestCommonDivisor(b, r, d);
        }
        assert gcd(a, b) == gcd(b, r);
        if r == 0 {
            assert gcd(b, r) == b;
            assert b >= d;
        }
        assert gcd(a, b) >= d;
    }
}

lemma GcdCoprimeEquiv(i: int, n: int)
    requires i >= 1 && n >= 1
    ensures coprime(i, n) <==> NoDivisor(i, n)
{
    GcdPositive(i, n);
    var g := gcd(i, n);
    assert g >= 1;
    GcdDivides(i, n);
    
    if coprime(i, n) {
        assert g == 1;
        forall j | 2 <= j <= i
            ensures !(n % j == 0 && i % j == 0)
        {
            if n % j == 0 && i % j == 0 {
                GcdIsGreatestCommonDivisor(i, n, j);
                assert false;
            }
        }
        assert NoDivisor(i, n);
    } else {
        assert g >= 2;
        assert i % g == 0 && n % g == 0;
        assert 2 <= g <= i;
        assert !NoDivisor(i, n);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
{
    if p == 2 {
        return 1;
    }
    
    var count := 0;
    var i := 1;
    
    ghost var S := set k | 1 <= k < i && NoDivisor(k, p-1);
    assert S == {};
    assert count == |S|;
    
    while i < p - 1
        invariant 1 <= i <= p - 1
        invariant S == set k | 1 <= k < i && NoDivisor(k, p-1)
        invariant count == |S|
    {
        var isCoprime := true;
        var j := 2;
        
        while j <= i && isCoprime
            invariant 2 <= j <= i + 1
            invariant isCoprime <==> (forall m :: 2 <= m < j ==> !((p-1) % m == 0 && i % m == 0))
        {
            if (p - 1) % j == 0 && i % j == 0 {
                isCoprime := false;
            }
            j := j + 1;
        }
        
        assert isCoprime <==> NoDivisor(i, p-1);
        
        if isCoprime {
            S := S + {i};
            count := count + 1;
        }
        
        i := i + 1;
    }
    
    assert S == set k | 1 <= k < p-1 && NoDivisor(k, p-1);
    
    return count;
}
// </vc-code>

