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
    assert a * b >= 2 * 2 == 4;
    assert a * b * c >= 4 * c >= 4 * 2 == 8;
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
    while i <= x
        invariant 2 <= i <= x + 1
        invariant forall a: nat, b: nat, c: nat :: 
            (Prime(a) && Prime(b) && Prime(c) && x == a * b * c && a < i) ==> false
    {
        if Prime(i) && x % i == 0 {
            var quotient1 := x / i;
            var j := 2;
            while j <= quotient1
                invariant 2 <= j <= quotient1 + 1
                invariant forall b: nat, c: nat :: 
                    (Prime(b) && Prime(c) && quotient1 == b * c && b < j) ==> false
            {
                if Prime(j) && quotient1 % j == 0 {
                    var k := quotient1 / j;
                    if Prime(k) {
                        assert x == i * j * k;
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

