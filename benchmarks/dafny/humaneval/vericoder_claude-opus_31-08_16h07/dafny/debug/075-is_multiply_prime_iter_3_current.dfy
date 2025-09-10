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

lemma NoSmallPrimeFactors(x: nat, bound: nat)
    requires bound > 1
    requires forall a: nat :: 2 <= a < bound && Prime(a) ==> x % a != 0
    ensures forall a: nat, b: nat, c: nat :: 
        Prime(a) && Prime(b) && Prime(c) && x == a * b * c ==> a >= bound || b >= bound || c >= bound
{
    forall a: nat, b: nat, c: nat | Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    ensures a >= bound || b >= bound || c >= bound
    {
        if a < bound && b < bound && c < bound {
            PrimeGreaterThanOne(a);
            assert a >= 2;
            assert Prime(a) && 2 <= a < bound;
            assert x % a != 0;
            assert x == a * b * c;
            assert x % a == 0;
            assert false;
        }
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
        invariant forall a: nat :: 2 <= a < i && Prime(a) ==> x % a != 0 || 
            exists b: nat, c: nat :: Prime(b) && Prime(c) && x == a * b * c
    {
        if i <= x && Prime(i) && x % i == 0 {
            var quotient1 := x / i;
            assert x == i * quotient1;
            
            var j := 2;
            while j * j <= quotient1
                invariant 2 <= j <= quotient1 + 1
                invariant forall b: nat :: 2 <= b < j && Prime(b) ==> quotient1 % b != 0
            {
                if j <= quotient1 && Prime(j) && quotient1 % j == 0 {
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
    
    // Prove the postcondition for the false case
    forall a: nat, b: nat, c: nat | Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    ensures false
    {
        PrimeGreaterThanOne(a);
        PrimeGreaterThanOne(b);
        PrimeGreaterThanOne(c);
        ProductBounds(a, b, c, x);
        
        if a * a * a <= x {
            assert 2 <= a < i;
            assert Prime(a) && x % a == 0;
            assert false;
        } else {
            assert a * a * a > x;
            assert a * b * c == x;
            assert a * a * a <= a * b * c;
            assert false;
        }
    }
}
// </vc-code>

