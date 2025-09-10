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
lemma CocGe(x: int, y: int, z: int)
  requires ValidInput(x, y, z)
  ensures (x + y) / z >= x / z + y / z
{
  var a := x % z;
  var b := y % z;
  var c := if a + b >= z then 1 else 0;
  assert (x + y) % z == (a + b) % z;
  assert (x + y) == (x - a) + (y - b) + (a + b);
  assert (x + y) / z == ((x - a) + (y - b) + (a + b)) / z;
  assert ((x - a) + (y - b)) % z == 0;
  assert (x - a) / z == x / z;
  assert (y - b) / z == y / z;
  assert (a + b) / z == c;
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
  assert coconuts == MaxCoconuts(x, y, z);
  var rx := x % z;
  var ry := y % z;
  if rx + ry < z {
    exchange := 0;
  } else {
    if rx > ry {
      exchange := z - rx;
    } else {
      exchange := z - ry;
    }
  }
  CocGe(x, y, z);
  assert coconuts >= (x / z) + (y / z);
  assert coconuts <= (x / z) + (y / z) + 1;
  assert 0 <= exchange < z;
}
// </vc-code>

