// SPEC

method random(a: int, b: int) returns (r: int)
// requires a <= b
 ensures a <= b ==> a <= r <= b
