//SPEC
method polyder (poly: array<real>, m: int) returns (ret: array<real>)
    requires m > 0
    ensures ret.Length == poly.Length - m 
{}