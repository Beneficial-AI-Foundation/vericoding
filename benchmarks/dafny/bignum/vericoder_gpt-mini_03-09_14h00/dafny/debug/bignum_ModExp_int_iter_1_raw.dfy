```vc-helpers
ghost lemma Exp_add(x: nat, m: nat, n: nat)
  ensures Exp_int(x, m + n) == Exp_int(x, m) * Exp_int(x, n)
{
  if n == 0 {
    // Exp_int(x, m+0) == Exp_int(x,m) * Exp_int(x,0) and Exp_int(x,0) == 1
    assert Exp_int(x, m + 0) == Exp_int(x, m);
    assert Exp_int(x, m) * Exp_int(x, 0) == Exp_int(x, m) * 1;
    assert Exp_int(x, 0) == 1;
  } else {
    // Inductive step: use n-1
    Exp_add(x, m, n - 1);
    // Exp_int(x, m + n) == x * Exp_int(x, m + n - 1)
    assert Exp_int(x, m + n) == x * Exp_int(x, m + n - 1);
    // by IH Exp_int(x, m + n - 1) == Exp_int(x, m) * Exp_int(x, n - 1)
    assert Exp_int(x, m + n - 1) == Exp_int(x, m) * Exp_int(x, n - 1);
    // combine
    assert x * Exp_int(x, m + n - 1) == Exp_int(x, m) * (x * Exp_int(x, n - 1));
    assert x * Exp_int(x, n - 1) == Exp_int(x, n);
    assert Exp_int(x, m) * (x * Exp_int(x, n - 1)) == Exp_int(x, m) * Exp_int(x, n);
  }
}

ghost lemma ModMul(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a % z * b % z) % z == (a * b) % z
{
  var q1 := a / z;
  var r1 := a % z;
  var q2 := b / z;
  var r2 := b % z;
  // a = z*q1 + r1, b = z*q2 + r2
  assert a == z * q1 + r1;
  assert b == z * q2 + r2;
  // (a*b) = z*(...) + r1*r2, hence (a*b) % z == (r1*r2) % z
  assert (a * b) == (z * q1 + r1) * (z * q2 + r2);
  // Expand: (z*q1 + r1)*(z*q2 + r2) = z*(...) + r1*r2
  // So (a*b) % z == (r1*r2) % z
  // But r1 == a%z and r2 == b%z, so left equals (a%z * b%z) % z
  assert (a % z * b % z) % z == (r1 * r2) % z;
  assert (a * b) % z == (r1 * r2) % z;
}

ghost lemma Div2Bound(y: nat, n: nat)
  requires y < Exp_int(2, n + 1)
  ensures y / 2 < Exp_int(2, n)
{
  var k := y / 2;
  // y == 2*k + (y % 2) implies 2*k <= y
  assert 2 * k <= y;
  // From 2*k <= y < Exp_int(2, n+1) we get 2*k < Exp_int(2, n+1)
  assert 2 * k < Exp_int(2, n + 1);
  // Use Exp_add to show Exp_int(2, n+1) == 2 * Exp_int(2, n)
  Exp_add(2, n, 1);
  assert Exp_int(2, n + 1) == 2 * Exp_int(2, n);
  // From 2*k < 2*Exp_int(2,n) we conclude k < Exp_int(2,n)
  if !(k < Exp_int(2, n)) {
    // assume contrary k >= Exp_int(2,n) then 2*k >= 2*Exp_int(2,n) contradicts 2*k < 2*Exp_int(2,n)
    assert k >= Exp_int(2, n);
    assert 2 * k >= 2 * Exp_int(2, n);
    // Contradiction with 2*k < Exp_int(2,n+1) == 2*Exp_int(2,n)
    assert false;
  }
}
```

```vc-code
{
  if n == 0 {
    if y == 0 {
      res := 1 % z;
    } else {
      // y must be 1 because y < Exp_int(2,1) == 2
      res := x % z;
    }
    return;
  }
  // split y into low bit and rest
  var y1 := y / 2;
  var y0 := y % 2;
  // ensure recursive precondition: y1 < 2^n
  Div2Bound(y, n);
  var t := ModExp_int(x, y1, n - 1, z);
  // t == Exp_int(x,y1) % z by postcondition
  var sq := (t * t) % z;
  // sq == (Exp_int(x,y1)*Exp_int(x,y1)) % z
  ModMul(t, t, z);
  // relate Exp_int(x, 2*y1) to product
  Exp_add(x, y1, y1);
  if y0 == 0 {
    // y == 2*y1
    res := sq;
    // sq == Exp_int(x,2*y1) % z == Exp_int(x,y) % z
    return;
  } else {
    // multiply by x and reduce
    var xm := x % z;
    ModMul(sq, xm, z);
    res := (sq * xm) % z;
    return;
  }
}
```