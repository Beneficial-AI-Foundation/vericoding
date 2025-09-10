predicate ValidInput(a: int, b: int, c: int, d: int, e: int, f: int)
{
    1 <= a < b <= 30 &&
    1 <= c < d <= 30 &&
    1 <= e <= 100 &&
    100 * a <= f <= 3000
}

predicate ValidSolution(a: int, b: int, c: int, d: int, e: int, f: int, total_mass: int, sugar_mass: int)
{
    total_mass > 0 && sugar_mass >= 0 &&
    total_mass <= f &&
    sugar_mass <= total_mass
}

function Density(total_mass: int, sugar_mass: int): int
    requires total_mass >= 0 && sugar_mass >= 0
{
    if total_mass > 0 then (100 * sugar_mass) / total_mass else 0
}

// <vc-helpers>
// <vc-helpers>
// No helpers required for this solution.
 // (kept intentionally for potential future lemmas)
 // </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int, e: int, f: int) returns (total_mass: int, sugar_mass: int)
    requires ValidInput(a, b, c, d, e, f)
    ensures ValidSolution(a, b, c, d, e, f, total_mass, sugar_mass)
    ensures total_mass >= 0 && sugar_mass >= 0
    ensures total_mass <= f
    ensures sugar_mass <= total_mass
    ensures exists water_units :: water_units > 0 && total_mass == water_units * 100 + sugar_mass
    ensures exists water_units :: water_units > 0 && sugar_mass <= water_units * e
    ensures exists i1, j1, i2, j2 :: 
        i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
        i1 <= 30 / a && j1 <= 30 / b &&
        i2 <= 3000 / c && j2 <= 3000 / d &&
        total_mass == (a * i1 + b * j1) * 100 + (c * i2 + d * j2) &&
        sugar_mass == c * i2 + d * j2 &&
        a * i1 + b * j1 > 0
    ensures total_mass > 0
// </vc-spec>
// <vc-code>
{
  ghost var bi1 := 1;
  ghost var bj1 := 0;
  ghost var bi2 := 0;
  ghost var bj2 := 0;

  var best_total := (a * 1 + b * 0) * 100;
  var best_sugar := 0;

  var max_i1 := 30 / a;
  var max_j1 := 30 / b;
  var max_i2 := 3000 / c;
  var max_j2 := 3000 / d;

  var i1 := 0;
  while i1 <= max_i1
    invariant 0 <= i1 <= max_i1 + 1
    invariant best_total >= 0 && best_sugar >= 0
  {
    var j1 := 0;
    while j1 <= max_j1
      invariant 0 <= j1 <= max_j1 + 1
      invariant best_total >= 0 && best_sugar >= 0
    {
      if i1 == 0 && j1 == 0 {
        j1 := j1 + 1;
        continue;
      }
      var water_units := a * i1 + b * j1;
      var water_grams := water_units * 100;
      if water_grams > f {
        j1 := j1 + 1;
        continue;
      }

      var i2 := 0;
      while i2 <= max_i2
        invariant 0 <= i2 <= max_i2 + 1
        invariant best_total >= 0 && best_sugar >= 0
      {
        var j2 := 0;
        while j2 <= max_j2
          invariant 0 <= j2 <= max_j2 + 1
          invariant best_total >= 0 && best_sugar >= 0
        {
          var sugar := c * i2 + d * j2;
          if sugar <= e * water_units && water_grams + sugar <= f {
            var cur_total := water_grams + sugar;
            if sugar * best_total > best_sugar * cur_total ||
               (sugar * best_total == best_sugar * cur_total && cur_total > best_total) {
              best_total := cur_total;
              best_sugar := sugar;
              bi1 := i1;
              bj1 := j1;
              bi2 := i2;
              bj2 := j2;
            }
          }
          j2 := j2 + 1;
        }
        i2 := i2 + 1;
      }

      j1 := j1 + 1;
    }
    i1 := i1 + 1;
  }

  total_mass := best_total;
  sugar_mass := best_sugar;

  // Basic properties
  assert total_mass > 0;
  assert sugar_mass >= 0;
  assert total_mass <= f;
  assert sugar_mass <= total_mass;

  // witness for water_units existence
  ghost var wu := a * bi1 + b * bj1;
  assert wu > 0;
  assert total_mass == wu * 100 + sugar_mass;
  assert sugar_mass <= wu * e;

  // Provide witnesses for the existential postconditions
  assert exists water_units :: water_units > 0 && total_mass == water_units * 100 + sugar_mass
    by { witness wu }
  assert exists i1, j1, i2, j2 ::
      i1 >= 0 && j1 >= 0 && i2 >= 0 && j2 >= 0 &&
      i1 <= 30 / a && j1 <= 30 / b &&
      i2 <= 3000 / c && j2 <= 3000 / d &&
      total_mass == (a * i1 + b * j1) * 100 + (c * i2 + d * j2) &&
      sugar_mass == c * i2 + d * j2 && a * i1 + b * j1 > 0
    by { witness bi1, bj1, bi2, bj2 }
}
// </vc-code>

