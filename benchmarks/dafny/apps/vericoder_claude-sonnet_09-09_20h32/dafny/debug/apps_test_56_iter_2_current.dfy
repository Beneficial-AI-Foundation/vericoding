predicate ValidInput(n: int, t: int) {
  1 <= n <= 10 && 0 <= t <= 10000
}

function TotalGlasses(n: int): int {
  n * (n + 1) / 2
}

predicate ValidResult(result: int, n: int, t: int) {
  result >= 0 && result <= TotalGlasses(n)
}

predicate CorrectForEdgeCases(result: int, n: int, t: int) {
  (t == 0 ==> result == 0) &&
  (n == 1 && t >= 1 ==> result == 1) &&
  (n == 1 && t == 0 ==> result == 0) &&
  (t >= 1 && n > 1 ==> result >= 1)
}

// <vc-helpers>
function GlassCapacity(): real { 1.0 }

function WaterInGlass(level: int, pos: int, n: int, t: int): real
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= n && 1 <= pos <= level
  decreases level, pos
{
  if level == 1 then
    t as real
  else if level == 2 then
    var overflow1 := if WaterInGlass(1, 1, n, t) > GlassCapacity() then WaterInGlass(1, 1, n, t) - GlassCapacity() else 0.0;
    overflow1 / 2.0
  else
    var leftParent := if pos > 1 then WaterInGlass(level - 1, pos - 1, n, t) else 0.0;
    var rightParent := if pos < level then WaterInGlass(level - 1, pos, n, t) else 0.0;
    var leftOverflow := if leftParent > GlassCapacity() then leftParent - GlassCapacity() else 0.0;
    var rightOverflow := if rightParent > GlassCapacity() then rightParent - GlassCapacity() else 0.0;
    (leftOverflow + rightOverflow) / 2.0
}

function CountFullGlassesInLevel(level: int, n: int, t: int): int
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= n
{
  if level == 1 then
    if WaterInGlass(1, 1, n, t) >= GlassCapacity() then 1 else 0
  else
    CountFullGlassesInLevelHelper(level, 1, level, n, t)
}

function CountFullGlassesInLevelHelper(level: int, pos: int, maxPos: int, n: int, t: int): int
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= n
  requires 1 <= pos <= maxPos + 1 <= level + 1
  decreases maxPos - pos
{
  if pos > maxPos then 0
  else
    var current := if WaterInGlass(level, pos, n, t) >= GlassCapacity() then 1 else 0;
    current + CountFullGlassesInLevelHelper(level, pos + 1, maxPos, n, t)
}

function CountAllFullGlasses(n: int, t: int): int
  requires 1 <= n <= 10 && 0 <= t <= 10000
{
  CountAllFullGlassesHelper(1, n, n, t)
}

function CountAllFullGlassesHelper(level: int, maxLevel: int, n: int, t: int): int
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= maxLevel + 1 <= n + 1
  decreases maxLevel - level
{
  if level > maxLevel then 0
  else
    CountFullGlassesInLevel(level, n, t) + CountAllFullGlassesHelper(level + 1, maxLevel, n, t)
}

lemma EdgeCaseProperties(n: int, t: int)
  requires ValidInput(n, t)
  ensures t == 0 ==> CountAllFullGlasses(n, t) == 0
  ensures n == 1 && t >= 1 ==> CountAllFullGlasses(n, t) == 1
  ensures n == 1 && t == 0 ==> CountAllFullGlasses(n, t) == 0
  ensures t >= 1 && n > 1 ==> CountAllFullGlasses(n, t) >= 1
{
  if t == 0 {
    assert WaterInGlass(1, 1, n, t) == 0.0;
    assert CountFullGlassesInLevel(1, n, t) == 0;
    assert CountAllFullGlasses(n, t) == 0;
  }
  if n == 1 && t >= 1 {
    assert WaterInGlass(1, 1, n, t) == t as real >= 1.0;
    assert CountFullGlassesInLevel(1, n, t) == 1;
    assert CountAllFullGlasses(n, t) == 1;
  }
  if t >= 1 && n > 1 {
    assert WaterInGlass(1, 1, n, t) == t as real >= 1.0;
    assert CountFullGlassesInLevel(1, n, t) >= 1;
    assert CountAllFullGlasses(n, t) >= 1;
  }
}

lemma ValidResultProperty(n: int, t: int)
  requires ValidInput(n, t)
  ensures 0 <= CountAllFullGlasses(n, t) <= TotalGlasses(n)
{
  assert CountAllFullGlasses(n, t) >= 0;
  assert CountAllFullGlasses(n, t) <= TotalGlasses(n);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, t: int) returns (result: int)
  requires ValidInput(n, t)
  ensures ValidResult(result, n, t)
  ensures CorrectForEdgeCases(result, n, t)
// </vc-spec>
// <vc-code>
{
  if t == 0 {
    result := 0;
  } else if n == 1 {
    result := 1;
  } else {
    EdgeCaseProperties(n, t);
    ValidResultProperty(n, t);
    result := CountAllFullGlasses(n, t);
  }
}
// </vc-code>

