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

lemma WaterInGlassZeroWhenTZero(level: int, pos: int, n: int, t: int)
  requires 1 <= n <= 10 && t == 0
  requires 1 <= level <= n && 1 <= pos <= level
  ensures WaterInGlass(level, pos, n, t) == 0.0
  decreases level, pos
{
  if level == 1 {
  } else if level == 2 {
    WaterInGlassZeroWhenTZero(1, 1, n, t);
  } else {
    if pos > 1 {
      WaterInGlassZeroWhenTZero(level - 1, pos - 1, n, t);
    }
    if pos < level {
      WaterInGlassZeroWhenTZero(level - 1, pos, n, t);
    }
  }
}

lemma CountNonNegative(n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  ensures CountAllFullGlasses(n, t) >= 0
{
  CountHelperNonNegative(1, n, n, t);
}

lemma CountHelperNonNegative(level: int, maxLevel: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= maxLevel + 1 <= n + 1
  ensures CountAllFullGlassesHelper(level, maxLevel, n, t) >= 0
  decreases maxLevel - level
{
  if level > maxLevel {
  } else {
    CountLevelNonNegative(level, n, t);
    CountHelperNonNegative(level + 1, maxLevel, n, t);
  }
}

lemma CountLevelNonNegative(level: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= n
  ensures CountFullGlassesInLevel(level, n, t) >= 0
{
  if level > 1 {
    CountLevelHelperNonNegative(level, 1, level, n, t);
  }
}

lemma CountLevelHelperNonNegative(level: int, pos: int, maxPos: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= n
  requires 1 <= pos <= maxPos + 1 <= level + 1
  ensures CountFullGlassesInLevelHelper(level, pos, maxPos, n, t) >= 0
  decreases maxPos - pos
{
  if pos > maxPos {
  } else {
    CountLevelHelperNonNegative(level, pos + 1, maxPos, n, t);
  }
}

lemma CountUpperBound(n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  ensures CountAllFullGlasses(n, t) <= TotalGlasses(n)
{
  CountHelperUpperBound(1, n, n, t);
}

lemma CountHelperUpperBound(level: int, maxLevel: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= maxLevel + 1 <= n + 1
  ensures CountAllFullGlassesHelper(level, maxLevel, n, t) <= TotalGlasses(maxLevel) - TotalGlasses(level - 1)
  decreases maxLevel - level
{
  if level > maxLevel {
  } else {
    CountLevelUpperBound(level, n, t);
    CountHelperUpperBound(level + 1, maxLevel, n, t);
  }
}

lemma CountLevelUpperBound(level: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= n
  ensures CountFullGlassesInLevel(level, n, t) <= level
{
  if level > 1 {
    CountLevelHelperUpperBound(level, 1, level, n, t);
  }
}

lemma CountLevelHelperUpperBound(level: int, pos: int, maxPos: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires 1 <= level <= n
  requires 1 <= pos <= maxPos + 1 <= level + 1
  ensures CountFullGlassesInLevelHelper(level, pos, maxPos, n, t) <= maxPos - pos + 1
  decreases maxPos - pos
{
  if pos > maxPos {
  } else {
    CountLevelHelperUpperBound(level, pos + 1, maxPos, n, t);
  }
}

lemma ZeroWaterProperty(n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires t == 0
  ensures CountAllFullGlasses(n, t) == 0
{
  WaterInGlassZeroWhenTZero(1, 1, n, t);
  ZeroWaterLevelProperty(1, n, t);
  ZeroWaterHelperProperty(1, n, n, t);
}

lemma ZeroWaterLevelProperty(level: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires t == 0 && 1 <= level <= n
  ensures CountFullGlassesInLevel(level, n, t) == 0
{
  if level > 1 {
    ZeroWaterLevelHelperProperty(level, 1, level, n, t);
  }
}

lemma ZeroWaterLevelHelperProperty(level: int, pos: int, maxPos: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires t == 0 && 1 <= level <= n
  requires 1 <= pos <= maxPos + 1 <= level + 1
  ensures CountFullGlassesInLevelHelper(level, pos, maxPos, n, t) == 0
  decreases maxPos - pos
{
  if pos <= maxPos {
    WaterInGlassZeroWhenTZero(level, pos, n, t);
    assert WaterInGlass(level, pos, n, t) == 0.0;
    assert 0.0 < GlassCapacity();
    ZeroWaterLevelHelperProperty(level, pos + 1, maxPos, n, t);
  }
}

lemma ZeroWaterHelperProperty(level: int, maxLevel: int, n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires t == 0 && 1 <= level <= maxLevel + 1 <= n + 1
  ensures CountAllFullGlassesHelper(level, maxLevel, n, t) == 0
  decreases maxLevel - level
{
  if level <= maxLevel {
    ZeroWaterLevelProperty(level, n, t);
    ZeroWaterHelperProperty(level + 1, maxLevel, n, t);
  }
}

lemma SingleGlassProperty(n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires n == 1 && t >= 1
  ensures CountAllFullGlasses(n, t) == 1
{
  assert WaterInGlass(1, 1, n, t) == t as real >= 1.0;
}

lemma PositiveWaterProperty(n: int, t: int)
  requires 1 <= n <= 10 && 0 <= t <= 10000
  requires t >= 1 && n > 1
  ensures CountAllFullGlasses(n, t) >= 1
{
  assert WaterInGlass(1, 1, n, t) == t as real >= 1.0;
  assert CountFullGlassesInLevel(1, n, t) >= 1;
  assert CountAllFullGlassesHelper(1, n, n, t) == CountFullGlassesInLevel(1, n, t) + CountAllFullGlassesHelper(2, n, n, t);
  CountHelperNonNegative(2, n, n, t);
}

lemma EdgeCaseProperties(n: int, t: int)
  requires ValidInput(n, t)
  ensures t == 0 ==> CountAllFullGlasses(n, t) == 0
  ensures n == 1 && t >= 1 ==> CountAllFullGlasses(n, t) == 1
  ensures n == 1 && t == 0 ==> CountAllFullGlasses(n, t) == 0
  ensures t >= 1 && n > 1 ==> CountAllFullGlasses(n, t) >= 1
{
  if t == 0 {
    ZeroWaterProperty(n, t);
  }
  if n == 1 && t >= 1 {
    SingleGlassProperty(n, t);
  }
  if t >= 1 && n > 1 {
    PositiveWaterProperty(n, t);
  }
}

lemma ValidResultProperty(n: int, t: int)
  requires ValidInput(n, t)
  ensures 0 <= CountAllFullGlasses(n, t) <= TotalGlasses(n)
{
  CountNonNegative(n, t);
  CountUpperBound(n, t);
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

