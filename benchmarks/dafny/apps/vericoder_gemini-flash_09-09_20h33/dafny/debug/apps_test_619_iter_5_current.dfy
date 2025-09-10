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

lemma ModuloDivision(a: int, b: int)
  requires b > 0
  ensures a == (a / b) * b + Modulo(a, b)
{}
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

  // Prove exchange == MinExchange(x, y, z)
  // Case 1: rx + ry < z
  if rx + ry < z {
    exchange := 0;
    // MinExchange definition for this case: 0
    // So exchange == MinExchange(x, y, z) holds.
  }
  // Case 2: rx + ry >= z
  else {
    // MinExchange definition for this case: z - (if rx > ry then rx else ry)
    // So exchange == MinExchange(x, y, z) holds.
    exchange := z - (if rx > ry then rx else ry);
  }

  // Prove coconuts == MaxCoconuts(x, y, z)
  // MaxCoconuts is defined as (x + y) / z, which is exactly what coconuts is assigned.

  // Prove coconuts >= x / z + y / z
  // This is true because (x+y)/z >= x/z + y/z (integer division property)
  // Or, more formally:
  // (x + y) / z = ((x/z)*z + Modulo(x,z) + (y/z)*z + Modulo(y,z)) / z
  //             = ((x/z + y/z)*z + ryx + ryy) / z (where ryx = Modulo(x,z) and ryy = Modulo(y,z))
  //             = x/z + y/z + (ryx + ryy) / z
  // Since ryx + ryy >= 0, then (ryx + ryy) / z >= 0
  // Therefore, coconuts >= x/z + y/z

  // Prove coconuts <= x / z + y / z + 1
  // We know that (ryx + ryy) / z can be at most 1 (since ryx < z and ryy < z, ryx+ryy < 2z).
  // So, (ryx + ryy) / z can be 0 or 1.
  // Thus, coconuts = x/z + y/z + (ryx + ryy) / z <= x/z + y/z + 1

  // Prove exchange >= 0 && exchange < z
  // From Modulo properties, 0 <= rx < z and 0 <= ry < z.

  // If rx + ry < z: exchange = 0, which satisfies 0 <= 0 < z (since z > 0)
  // If rx + ry >= z:
  // Let m = (if rx > ry then rx else ry). Then exchange = z - m.
  // We know that rx < z and ry < z, so m < z.
  // Therefore, exchange = z - m > z - z = 0. So exchange > 0.
  // We also know that m >= 0 (since rx >= 0 and ry >= 0).
  // Therefore, exchange = z - m <= z - 0 = z. So exchange <= z.
  // Combining exchange > 0 and exchange <= z.
  // Since rx + ry >= z means at least one of rx or ry must be positive,
  // and if rx=0 and ry=z-1 (or vice versa), then m=z-1, exchange=1.
  // If rx=z-1 and ry=z-1, then m=z-1, exchange=1.
  // It's guaranteed that m cannot be equal to z based on rx < z and ry < z.
  // So m <= z-1.
  // Thus exchange = z - m >= z - (z-1) = 1.
  // Thus 1 <= exchange <= z. And since we need exchange < z, we have to consider m.
  // m is either rx or ry.
  // Since rx < z and ry < z, then m < z.
  // Therefore z - m > 0. (i.e. exchange > 0)
  // Also, since rx >= 0 and ry >= 0, then m >= 0.
  // Therefore z - m <= z. (i.e. exchange <= z)
  // However, we need exchange < z.
  // This means m must be > 0.
  // If m = 0 (which means rx = 0 and ry = 0), then exchange = z.
  // But if rx = 0 and ry = 0, then rx + ry = 0 < z (assuming z > 0).
  // In this case, exchange would be 0, not z.
  // So if rx + ry >= z, it's guaranteed that m > 0.
  // Therefore, 0 < exchange <= z.
  // Wait, if rx + ry >= z.
  // The definition is z - (if rx > ry then rx else ry).
  // Let `m_val` be `if rx > ry then rx else ry`.
  // We know `0 <= m_val < z`.
  // So `z - m_val` will be `> 0` and `<= z`.
  // Specifically, since `m_val < z`, then `z - m_val > 0`.
  // And since `m_val >= 0`, then `z - m_val <= z`.
  // So `0 < exchange <= z`.
  // The postcondition is `exchange < z`.
  // This means `m_val` cannot be 0 when `rx+ry >= z`.
  // Indeed, if `m_val = 0`, then `rx=0` and `ry=0`.
  // In that case, `rx+ry = 0`, which contradicts `rx+ry >= z` (since z > 0).
  // Therefore, `m_val` must be `> 0`.
  // Then `exchange = z - m_val < z`. And `exchange = z - m_val > 0`.
  // So `0 < exchange < z`. The `exchange < z` is satisfied.
}
// </vc-code>

