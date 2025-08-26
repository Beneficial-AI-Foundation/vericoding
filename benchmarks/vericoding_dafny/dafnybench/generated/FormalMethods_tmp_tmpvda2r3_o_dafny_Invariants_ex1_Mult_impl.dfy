method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
// </vc-spec>
// <vc-code>
{
  var m := x;
  var n := y;
  r := 0;
  
  while m > 0
    invariant m * n + r == x * y
    invariant m >= 0
    decreases m
  {
    r := r + n;
    m := m - 1;
  }
  
  // After the loop, we know !(m > 0), which means m <= 0
  // Since m is a nat (m >= 0), this means m == 0
  assert m <= 0;
  assert m >= 0; // m is a nat
  assert m == 0;
  assert m * n + r == x * y;
  assert 0 * n + r == x * y;
  assert r == x * y;
}
// </vc-code>

/*
Inv = m*n + r = x*y
Mult(5,3)
Teste de mesa
x   y   m   n   r       Inv --> m*n + r = x*y
5   3   5   3   0       5x3+0 = 5*3
5   3   4   3   3       4x3+3 = 5*3
5   3   3   3   6       3x3+6 = 5*3
5   3   2   3   9       2x3+9 = 5*3
5   3   1   3   12      1x3+12 = 5*3
5   3   0   3   15      0x3+15 = 5*3
*/