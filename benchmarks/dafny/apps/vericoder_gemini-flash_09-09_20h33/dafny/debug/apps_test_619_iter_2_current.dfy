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
function Modulo(a: int, b: int): int
  requires b > 0
  ensures 0 <= Modulo(a, b) < b
{
  var r := a % b;
  if r < 0 then r + b else r
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
  var rx := Modulo(x, z);
  var ry := Modulo(y, z);

  if rx + ry < z then
    exchange := 0;
  else
    exchange := z - Modulo(if rx > ry then rx else ry, z);
}
// </vc-code>

