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
lemma mod_lemma(a: int, b: int)
  requires b > 0
  ensures a % b >= 0 && a % b < b
{
}

lemma div_lemma(a: int, b: int)
  requires b > 0
  ensures a / b * b <= a < (a / b + 1) * b
{
}

lemma sum_mod_lemma(x: int, y: int, z: int)
  requires z > 0
  ensures (x % z + y % z) / z == (x % z + y % z >= z ? 1 : 0)
{
  var rx := x % z;
  var ry := y % z;
  if rx + ry < z {
    assert (rx + ry) / z == 0;
  } else {
    assert rx + ry >= z;
    assert (rx + ry) / z == 1;
    assert rx + ry < 2*z; // because rx < z and ry < z
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
  var total := x + y;
  
  coconuts := total / z;
  
  if rx + ry < z {
    exchange := 0;
  } else {
    var max_remainder := if rx > ry then rx else ry;
    exchange := z - max_remainder;
  }
}
// </vc-code>

