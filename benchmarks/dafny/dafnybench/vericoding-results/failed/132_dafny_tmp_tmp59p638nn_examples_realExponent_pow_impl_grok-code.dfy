ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0

// <vc-helpers>
ghost function Power(r: real, e: nat): real
  requires r > 0.0 && e >= 0
  ensures Power(r,e) > 0.0
  decreases e
{
  if e == 0 then 1.0
  else r * Power(r, e-1)
}

ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0
{
  Power(n, alpha as nat)
}

ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0
// </vc-helpers>

// <vc-spec>
method pow(n: nat, alpha: real) returns (product: real)
    requires n > 0
    requires alpha > 0.0
    ensures product == power(n as real, alpha)
// </vc-spec>
// <vc-code>
{
  var r := n as real;
  var e := alpha as nat;
  product := 1.0;
  var i := 1;
  while i <= e
    invariant 1 <= i <= e + 1 && product >= 0.0
    invariant product == Power(r, i - 1)
  {
    product := product * r;
    i := i + 1;
  }
}
// </vc-code>

