function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
lemma PrimeGreaterThanOne(p: nat)
    requires Prime(p)
    ensures p > 1
{
}

lemma ProductBounds(a: nat, b: nat, c: nat, x: nat)
    requires a > 1 && b > 1 && c > 1
    requires x == a * b * c
    ensures a <= x && b <= x && c <= x
{
    assert b >= 2 && c >= 2;
    assert x == a * b * c >= a * 2 * 2 == 4 * a >= 2 * a > a;
    assert x >= a;
    
    assert a >= 2 && c >= 2;
    assert x == a * b * c >= 2 * b * 2 == 4 * b >= 2 * b > b;
    assert x >= b;
    
    assert a >= 2 && b >= 2;
    assert x == a * b * c >= 2 * 2 * c == 4 * c >= 2 * c > c;
    assert x >= c;
}

lemma TripleProductExists(x: nat, i: nat, j: nat, k: nat)
    requires Prime(i) && Prime(j) && Prime(k)
    requires x == i * j * k
    ensures exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
{
    assert Prime(i) && Prime(j) && Prime(k) && x == i * j * k;
}

lemma SmallestPrimeFactor(a: nat, b: nat, c: nat, x: nat)
    requires Prime(a) && Prime(b) && Prime(c)
    requires x == a * b * c
    ensures a * a * a <= x || b * b * b <= x || c * c * c <= x
{
    PrimeGreaterThanOne(a);
    PrimeGreaterThanOne(b);
    PrimeGreaterThanOne(c);
    
    if a * a * a > x && b * b * b > x && c * c * c > x {
        assert a * a * a > a * b * c;
        assert a * a > b * c;
        assert b * b * b > a * b * c;
        assert b * b > a * c;
        assert c * c * c > a * b * c;
        assert c * c > a * b;
        
        assert a * a > b * c && b * b > a * c && c * c > a * b;
        assert a * a * b * b > a * b * c * c;
        assert a * b > c * c;
        assert c * c > a * b;
        assert false;
    }
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var i := 2;
    while i * i * i <= x
        invariant 2 <= i <= x + 1
        invariant forall a: nat, b: nat, c: nat :: 
            Prime(a) && Prime(b) && Prime(c) && x == a * b * c && a < i ==> false
    {
        if Prime(i) && x % i == 0 {
            var quotient1 := x / i;
            assert x == i * quotient1;
            
            var j := 2;
            while j * j <= quotient1
                invariant 2 <= j <= quotient1 + 1
                invariant forall b: nat :: 2 <= b < j && Prime(b) ==> quotient1 % b != 0
            {
                if Prime(j) && quotient1 % j == 0 {
                    var k := quotient1 / j;
                    assert quotient1 == j * k;
                    assert x == i * j * k;
                    
                    if k > 1 && Prime(k) {
                        TripleProductExists(x, i, j, k);
                        ans := true;
                        return;
                    }
                }
                j := j + 1;
            }
        }
        i := i + 1;
    }
    
    ans := false;
    
    forall a: nat, b: nat, c: nat | Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    ensures false
    {
        SmallestPrimeFactor(a, b, c, x);
        if a * a * a <= x {
            assert a < i;
            assert false;
        } else if b * b * b <= x {
            assert b < i;
            assert false;
        } else {
            assert c * c * c <= x;
            assert c < i;
            assert false;
        }
    }
}
// </vc-code>

