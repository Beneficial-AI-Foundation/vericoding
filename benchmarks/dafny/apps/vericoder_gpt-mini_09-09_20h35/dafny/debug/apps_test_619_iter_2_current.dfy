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
    assert x + y == (qx + qy) * z + s;
    assert (x + y) / z == qx + qy;
    assert (x + y) % z == s;
    assert (x + y) / z == x / z + y / z + 0;
  } else {
    // s >= z
    assert s == z + (s - z);
    assert s - z < z;
    assert x + y == (qx + qy + 1) * z + (s - z);
    assert (x + y) / z == qx + qy + 1;
    assert (x + y) % z == s - z;
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
    ModBounds(x, z);
    ModBounds(y, z);
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

