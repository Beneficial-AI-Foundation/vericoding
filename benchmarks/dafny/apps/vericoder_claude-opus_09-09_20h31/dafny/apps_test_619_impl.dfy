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
lemma MinExchangeProperties(x: int, y: int, z: int)
  requires ValidInput(x, y, z)
  ensures var rx := x % z; var ry := y % z;
          MinExchange(x, y, z) == if rx + ry < z then 0 else z - if rx > ry then rx else ry
  ensures MinExchange(x, y, z) >= 0
  ensures MinExchange(x, y, z) < z
{
  var rx := x % z;
  var ry := y % z;
  assert rx >= 0 && rx < z;
  assert ry >= 0 && ry < z;
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

lemma DivModProperties(a: int, b: int)
  requires b > 0
  ensures a == (a / b) * b + (a % b)
  ensures 0 <= a % b < b
{}

lemma MaxCoconutsBounds(x: int, y: int, z: int)
  requires ValidInput(x, y, z)
  ensures MaxCoconuts(x, y, z) >= x / z + y / z
  ensures MaxCoconuts(x, y, z) <= x / z + y / z + 1
{
  var rx := x % z;
  var ry := y % z;
  
  assert 0 <= rx < z;
  assert 0 <= ry < z;
  assert 0 <= rx + ry < 2 * z;
  
  calc == {
    x + y;
    (x / z) * z + rx + (y / z) * z + ry;
    (x / z + y / z) * z + (rx + ry);
  }
  
  if rx + ry < z {
    assert (x + y) / z == x / z + y / z;
  } else {
    assert rx + ry >= z;
    assert rx + ry < 2 * z;
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
  coconuts := (x + y) / z;
  
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
  
  MinExchangeProperties(x, y, z);
  MaxCoconutsBounds(x, y, z);
}
// </vc-code>

