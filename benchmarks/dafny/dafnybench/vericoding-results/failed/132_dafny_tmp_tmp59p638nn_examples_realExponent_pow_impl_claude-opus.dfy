ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0

// <vc-helpers>
lemma PowerOne(alpha: real)
    requires alpha > 0.0
    ensures power(1.0, alpha) == alpha

lemma PowerSucc(n: nat, alpha: real)
    requires n > 0
    requires alpha > 0.0
    ensures power((n + 1) as real, alpha) == power(n as real, alpha) * alpha

lemma PowerBase(n: nat, alpha: real)
    requires n > 0
    requires alpha > 0.0
    ensures n == 1 ==> power(n as real, alpha) == alpha
    ensures n > 1 ==> power(n as real, alpha) == power((n - 1) as real, alpha) * alpha
{
    if n == 1 {
        PowerOne(alpha);
    } else {
        assert n > 1;
        assert (n - 1) + 1 == n;
        PowerSucc(n - 1, alpha);
    }
}
// </vc-helpers>

// <vc-spec>
method pow(n: nat, alpha: real) returns (product: real)
    requires n > 0
    requires alpha > 0.0
    ensures product == power(n as real, alpha)
// </vc-spec>
// <vc-code>
{
    product := alpha;
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant product == power(i as real, alpha)
        invariant alpha > 0.0
    {
        PowerSucc(i, alpha);
        product := product * alpha;
        i := i + 1;
    }
    
    assert i == n;
    assert product == power(n as real, alpha);
}
// </vc-code>

