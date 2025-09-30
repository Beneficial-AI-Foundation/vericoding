predicate ValidInput(x: int, y: int, z: int)
{
  x >= 0 && y >= 0 && z > 0
}

function MaxCoconuts(x: int, y: int, z: int): int
  requires ValidInput(x, y, z)
{
  (x + y) / z
}

function MinExchange(x: int, y: int, z: int): int
  requires ValidInput(x, y, z)
{
  var rx := x % z;
  var ry := y % z;
  if rx + ry < z then 0
  else z - if rx > ry then rx else ry
}

// <vc-helpers>
lemma ModBounds(x:int, z:int)
  requires z > 0
  ensures 0 <= x % z < z
{
  var q := x / z;
  var r := x % z;
  assert x == q * z + r;
  assert 0 <= r < z;
}

lemma DivModUniq(a:int, q:int, r:int, z:int)
  requires z > 0
  requires 0 <= r < z
  requires a == q * z + r
  ensures a / z == q
  ensures a % z == r
{
  var q2 := a / z;
  var r2 := a % z;
  assert a == q2 * z + r2;
  assert 0 <= r2 < z;
  assert q * z + r == q2 * z + r2;
  assert (q - q2) * z == r2 - r;
  assert -z < r2 - r < z;
  if q2 > q {
    // then q2 - q >= 1, so (q - q2)*z <= -z, contradicting r2 - r > -z
    assert q2 >= q + 1;
    assert q - q2 <= -1;
    assert (q - q2) * z <= -1 * z;
    assert (q - q2) * z <= -z;
    assert (q - q2) * z == r2 - r;
    assert r2 - r <= -z;
    assert false;
  } else if q2 < q {
    // then q - q2 >= 1, so (q - q2)*z >= z, contradicting r2 - r < z
    assert q >= q2 + 1;
    assert q - q2 >= 1;
    assert (q - q2) * z >= 1 * z;
    assert (q - q2) * z >= z;
    assert (q - q2) * z == r2 - r;
    assert r2 - r >= z;
    assert false;
  }
  // hence q2 == q and r2 == r
  assert q2 == q;
  assert r2 == r;
}

lemma DivModSum(x:int, y:int, z:int)
  requires ValidInput(x, y, z)
  ensures (x + y) / z == x / z + y / z + (if x % z + y % z >= z then 1 else 0)
  ensures (x + y) % z == (if x % z + y % z < z then x % z + y % z else x % z + y % z - z)
{
  var qx := x / z;
  var rx := x % z;
  var qy := y / z;
  var ry := y % z;
  assert x == qx * z + rx;
  assert y == qy * z + ry;
  assert 0 <= rx < z;
  assert 0 <= ry < z;
  var s := rx + ry;
  if s < z {
    assert 0 <= s < z;
    assert x + y == (qx + qy) * z + s;
    DivModUniq(x + y, qx + qy, s, z);
    assert (x + y) / z == qx + qy;
    assert (x + y) % z == s;
    assert (x + y) / z == x / z + y / z + 0;
  } else {
    // s >= z
    var s2 := s - z;
    assert 0 <= s2 < z;
    assert x + y == (qx + qy + 1) * z + s2;
    DivModUniq(x + y, qx + qy + 1, s2, z);
    assert (x + y) / z == qx + qy + 1;
    assert (x + y) % z == s2;
    assert (x + y) / z == x / z + y / z + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int, z: int) returns (coconuts: int, exchange: int)
  requires ValidInput(x, y, z)
  ensures coconuts == MaxCoconuts(x, y, z)
  ensures exchange == MinExchange(x, y, z)
  ensures coconuts >= x / z + y / z
  ensures coconuts <= x / z + y / z + 1
  ensures exchange >= 0 && exchange < z
// </vc-spec>
// <vc-code>
{
  var rx := x % z;
  var ry := y % z;
  var s := rx + ry;
  if s < z {
    coconuts := x / z + y / z;
    exchange := 0;
    DivModSum(x, y, z);
    assert coconuts == MaxCoconuts(x, y, z);
    assert exchange == MinExchange(x, y, z);
    assert exchange >= 0 && exchange < z;
  } else {
    coconuts := x / z + y / z + 1;
    assert 0 <= rx < z;
    assert 0 <= ry < z;
    if rx > ry {
      exchange := z - rx;
      assert rx + ry >= z;
      assert rx >= z - ry;
      assert rx <= z - 1;
      assert z - rx >= 1;
      assert exchange >= 0 && exchange < z;
    } else {
      exchange := z - ry;
      assert rx + ry >= z;
      assert ry >= z - rx;
      assert ry <= z - 1;
      assert z - ry >= 1;
      assert exchange >= 0 && exchange < z;
    }
    DivModSum(x, y, z);
    assert coconuts == MaxCoconuts(x, y, z);
    assert exchange == MinExchange(x, y, z);
  }
}
// </vc-code>

