// SPEC

method sqrt(x: real) returns (r: real)
 requires x >= 0.0
 ensures r * r == x && r >= 0.0
