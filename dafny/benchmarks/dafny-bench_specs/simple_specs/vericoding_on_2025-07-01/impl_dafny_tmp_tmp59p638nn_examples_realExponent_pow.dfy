//ATOM

ghost function power(n: real, alpha: real): real
  requires n > 0.0 && alpha > 0.0
  ensures power(n, alpha) > 0.0


// SPEC

method pow(n: nat, alpha: real) returns (product: real)
  requires n > 0
  requires alpha > 0.0
  ensures product == power(n as real, alpha)
{
}