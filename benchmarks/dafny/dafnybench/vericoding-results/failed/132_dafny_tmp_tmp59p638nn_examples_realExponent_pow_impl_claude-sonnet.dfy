ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0

// <vc-helpers>
ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0

lemma PowerPositive(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0
{
}

lemma PowerOfNat(n: nat, alpha: real)
    requires n > 0 && alpha > 0.0
    ensures power(n as real, alpha) > 0.0
{
    PowerPositive(n as real, alpha);
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
    product := power(n as real, alpha);
}
// </vc-code>

