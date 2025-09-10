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

lemma GcdCoprimeEquiv(i: int, n: int)
    requires i >= 1 && n >= 1
    ensures coprime(i, n) <==> NoDivisor(i, n)
{
    if coprime(i, n) {
        // If gcd(i, n) == 1, then no common divisor > 1 exists
        assert NoDivisor(i, n);
    } else {
        // If gcd(i, n) > 1, then there exists a common divisor
        var g := gcd(i, n);
        assert g > 1;
        assert i % g == 0 && n % g == 0;
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
    
    ghost var S := set k | 1 <= k < i && (forall j :: 2 <= j <= k ==> !((p-1) % j == 0 && k % j == 0));
    assert S == {};
    assert count == |S|;
    
    while i < p - 1
        invariant 1 <= i <= p - 1
        invariant S == set k | 1 <= k < i && (forall j :: 2 <= j <= k ==> !((p-1) % j == 0 && k % j == 0))
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
        
        assert isCoprime <==> (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0));
        
        if isCoprime {
            S := S + {i};
            count := count + 1;
        }
        
        i := i + 1;
    }
    
    assert S == set k | 1 <= k < p-1 && (forall j :: 2 <= j <= k ==> !((p-1) % j == 0 && k % j == 0));
    
    return count;
}
// </vc-code>

