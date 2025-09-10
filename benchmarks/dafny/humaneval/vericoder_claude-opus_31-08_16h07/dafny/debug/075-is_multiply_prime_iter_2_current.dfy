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
    // Since a, b, c > 1, we have:
    // x = a * b * c >= a * 2 * 2 = 4a > a (since a >= 2)
    assert b >= 2 && c >= 2;
    assert x == a * b * c >= a * 2 * 2 == 4 * a >= 2 * a > a;
    assert x >= a;
    
    // Similarly for b:
    assert a >= 2 && c >= 2;
    assert x == a * b * c >= 2 * b * 2 == 4 * b >= 2 * b > b;
    assert x >= b;
    
    // And for c:
    assert a >= 2 && b >= 2;
    assert x == a * b * c >= 2 * 2 * c == 4 * c >= 2 * c > c;
    assert x >= c;
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
        invariant 2 <= i
        invariant forall a: nat, b: nat, c: nat :: 
            (Prime(a) && Prime(b) && Prime(c) && x == a * b * c && a < i) ==> false
    {
        if Prime(i) && x % i == 0 {
            var quotient1 := x / i;
            var j := 2;
            while j * j <= quotient1
                invariant 2 <= j
                invariant forall b: nat, c: nat :: 
                    (Prime(b) && Prime(c) && quotient1 == b * c && b < j) ==> false
            {
                if Prime(j) && quotient1 % j == 0 {
                    var k := quotient1 / j;
                    if Prime(k) {
                        assert x == i * j * k;
                        assert Prime(i) && Prime(j) && Prime(k);
                        PrimeGreaterThanOne(i);
                        PrimeGreaterThanOne(j);
                        PrimeGreaterThanOne(k);
                        ProductBounds(i, j, k, x);
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
}
// </vc-code>

