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
lemma DivisionProperties(x: int, y: int, z: int)
  requires ValidInput(x, y, z)
  ensures (x + y) / z >= x / z + y / z
  ensures (x + y) / z <= x / z + y / z + 1
{
  var rx := x % z;
  var ry := y % z;
  
  assert x == (x / z) * z + rx;
  assert y == (y / z) * z + ry;
  assert 0 <= rx < z;
  assert 0 <= ry < z;
  
  if rx + ry < z {
    assert (rx + ry) / z == 0;
    assert (x + y) / z == x / z + y / z;
  } else {
    assert rx + ry >= z;
    assert rx + ry < 2 * z;
    assert (rx + ry) / z == 1;
    assert (x + y) / z == x / z + y / z + 1;
  }
}

lemma MinExchangeBounds(x: int, y: int, z: int)
  requires ValidInput(x, y, z)
  ensures MinExchange(x, y, z) >= 0
  ensures MinExchange(x, y, z) < z
{
  var rx := x % z;
  var ry := y % z;
  
  if rx + ry < z {
    assert MinExchange(x, y, z) == 0;
  } else {
    var maxRem := if rx > ry then rx else ry;
    assert maxRem < z;
    assert MinExchange(x, y, z) == z - maxRem;
    assert MinExchange(x, y, z) > 0;
    assert MinExchange(x, y, z) < z;
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
  coconuts := (x + y) / z;
  
  var rx := x % z;
  var ry := y % z;
  
  if rx + ry < z {
    exchange := 0;
  } else {
    exchange := z - if rx > ry then rx else ry;
  }
  
  DivisionProperties(x, y, z);
  MinExchangeBounds(x, y, z);
}
// </vc-code>

