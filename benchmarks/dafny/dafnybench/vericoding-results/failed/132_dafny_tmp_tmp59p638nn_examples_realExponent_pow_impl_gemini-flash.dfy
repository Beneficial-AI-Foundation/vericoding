ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0

// <vc-helpers>
ghost function realPower(n: real, alpha: real): real
    requires n >= 1.0 && alpha > 0.0
    ensures realPower(n, alpha) == power(n, alpha)
    decreases n
{
    if n == 1.0 then
        alpha
    else
        calc {
            alpha * realPower(n - 1.0, alpha);
        ==  { assert n - 1.0 >= 0.0;
              assert n -1.0 == (n as int) as real - 1.0;
              assert (n as int) - 1 > 0 ==> (n as int) -1 >= 1;
              assert (n as int) - 1 == 0 ==> n as int == 1;
              power(n - 1.0, alpha.truncate_to_real); }
            alpha * power(n - 1.0, alpha);
        ==  power(n, alpha);
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
    if n == 1 {
        return alpha;
    } else {
        var res := pow(n - 1, alpha);
        return alpha * res;
    }
}
// </vc-code>

