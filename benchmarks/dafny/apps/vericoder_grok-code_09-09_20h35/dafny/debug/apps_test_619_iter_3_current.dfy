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
// No changes needed
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
  assert coconuts == MaxCoconuts(x, y, z);
  var rx := x % z;
  var ry := y % z;
  if rx + ry < z {
    exchange := 0;
    assert exchange == MinExchange(x, y, z);
  } else {
    if rx > ry {
      exchange := z - rx;
    } else {
      exchange := z - ry;
    }
    assert exchange == MinExchange(x, y, z);
  }
  assert coconuts >= (x / z) + (y / z);
  assert coconuts <= (x / z) + (y / z) + 1;
  assert 0 <= exchange < z;
}
// </vc-code>

