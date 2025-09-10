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
  ensures (x % z + y % z) / z == (if x % z + y % z >= z then 1 else 0)
{
  var rx := x % z;
  var ry := y % z;
  if rx + ry < z {
    assert (rx + ry) / z == 0;
  } else {
    assert rx + ry >= z;
    mod_lemma(x, z);
    mod_lemma(y, z);
    assert rx < z && ry < z;
    assert rx + ry < 2*z;
    assert (rx + ry) / z == 1;
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
  
  mod_lemma(x, z);
  mod_lemma(y, z);
  
  coconuts := total / z;
  
  if rx + ry < z {
    exchange := 0;
    assert exchange == MinExchange(x, y, z);
  } else {
    var max_remainder := if rx > ry then rx else ry;
    exchange := z - max_remainder;
    assert exchange == MinExchange(x, y, z);
  }
  
  // Postcondition verification aids
  assert coconuts == MaxCoconuts(x, y, z);
  div_lemma(total, z);
  assert coconuts >= x / z + y / z;
  assert coconuts <= x / z + y / z + 1;
  assert exchange >= 0 && exchange < z;
}
// </vc-code>

