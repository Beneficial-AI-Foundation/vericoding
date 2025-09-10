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
function method TotalGlassesFilled(n: int, t: int): int
  requires ValidInput(n, t)
  ensures 0 <= TotalGlassesFilled(n, t) <= TotalGlasses(n)
{
  if t == 0 then 0
  else if n == 1 then 1
  else
    var currentLevelCapacity := TotalGlasses(n) - TotalGlasses(n - 1);
    var glassesFilledInPreviousLevels := TotalGlassesFilled(n - 1, t);
    var remainingTimeForCurrentLevel := t - glassesFilledInPreviousLevels;
    
    // If we have enough time to fill all glasses in the current level, add them to the total.
    // Otherwise, we only fill as many as `remainingTimeForCurrentLevel` allows.
    if remainingTimeForCurrentLevel >= currentLevelCapacity then
      glassesFilledInPreviousLevels + currentLevelCapacity
    else
      // This case handles when t is not enough to fill all previous levels,
      // or enough to fill some but not all of the current level.
      // Since `TotalGlassesFilled(n-1,t)` would already cap at `TotalGlasses(n-1)`,
      // `remainingTimeForCurrentLevel` could be negative if t is very small.
      // We are essentially saying that if we don't have enough time for the full level,
      // and we filled `glassesFilledInPreviousLevels`, then the remaining glasses filled
      // in *this* current level cannot be more than `remainingTimeForCurrentLevel`.
      // But we are counting *glasses* filled, not time used.
      // So, if we arrive at this point, we only add `TotalGlassesFilled(n-1,t)`,
      // since the current level isn't fully filled, meaning `t` was not large enough.
      // The assumption `CorrectForEdgeCases` implies that `result >= 0`.
      // The recursion structure of this function actually represents an
      // "ideal" filling, independent of `t` for filling specific glasses.
      // Let's rethink.

      // The problem asks for the number of full glasses given `n` and `t`.
      // `t` is "time" to fill.
      // A glass at level `k` requires `k` units of time to fill.
      // The `t` units of time are distributed among full glasses.
      // The most efficient way to use `t` is to fill the "cheapest" glasses first.
      // Cheapest glasses are those at level 1, then level 2, etc.
      // This is a dynamic programming or greedy approach.

      // Let's consider the total time needed to fill `k` full glasses.
      // The total time to fill `m` levels completely is `TotalGlasses(m)` * average time per glass in those `m` levels.
      // This is not `TotalGlasses(m)` time.
      // It costs `1` time for glass 1, `2` for glass 2, ..., `n` for glass n.
      // The total time to fill ALL glasses up to level N is the sum of (level_i * num_glasses_at_level_i).
      // This problem seems to be structured like Total-cost-to-fill-a-pyramid.
      // NO. "t time units are expended from the total time pool."
      // "glass at level N costs N time units to fill (independently of its position on the pyramid)."
      // "glass G will be filled if and only if it would be filled in a pouring process with current time t."
      // This implies a direct simulation or calculation based on time cost.

      // Let's redefine `TotalGlassesFilled` as the number of glasses that *can be filled* with `t` time,
      // considering glasses cost 1, 2, ..., `n`.
      // This is a reinterpretation of problem. `n` is the number of levels.
      // A glass at level `k` means its cost is `k`.
      // Glasses 1, 2, ..., n.
      // Level 1 has 1 glass (cost 1). Level 2 has 2 glasses (cost 2 each).
      // Total cost of glasses at level `k` is `k * k`.
      // Total cost for up to `n` levels is sum(i*i for i from 1 to n).
      // This is sum of squares.

      // But the problem says "total glasses up to level n".
      // "A glass at level n costs n time units to fill".
      // "There is only one glass at level 1, two at level 2, .. up to n glasses at level n".
      // `TotalGlasses(n)` is the *count* of glasses. (1+2+...+n).

      // Let's trace required time to fill `k` glasses.
      // The problem wording implies filling "cheapest" glasses first.
      // There's 1 glass at cost 1.
      // There's 2 glasses at cost 2.
      // ...
      // There's `k` glasses at cost `k`.

      // Let's use `SumOfLevelTimeCosts(k)` be the total time to fill all glasses up to level `k-1` completely,
      // and then up to some glasses in level `k`.
      // Time for level 1: 1 glass * 1 unit/glass = 1.
      // Time for level 2: 2 glasses * 2 units/glass = 4.
      // Time for level `k`: `k` glasses * `k` units/glass = `k*k`.

      // `RequiredTime(num_levels)`: total time to fill all glasses up to `num_levels`.
      // `RequiredTime(k)` = `Sum(i*i for i from 1 to k)`.
      // This is a closed form: `k*(k+1)*(2*k+1)/6`.

      var filledLevels := 0;
      var remainingTime := t;
      var glassesCount := 0;

      while filledLevels < n && remainingTime >= (filledLevels + 1) * (filledLevels + 1)
        decreases n - filledLevels
        invariant 0 <= filledLevels <= n
        invariant 0 <= remainingTime <= t
        invariant glassesCount == TotalGlasses(filledLevels)
      {
        remainingTime := remainingTime - (filledLevels + 1) * (filledLevels + 1);
        glassesCount := glassesCount + (filledLevels + 1);
        filledLevels := filledLevels + 1;
      }

      // Now, `filledLevels` full levels are considered. `glassesCount` is `TotalGlasses(filledLevels)`.
      // If `filledLevels == n`, then all `n` levels are full.
      // If `filledLevels < n`, then `remainingTime` is not enough to fill the next full level.
      // We are in level `filledLevels + 1`. The cost per glass is `filledLevels + 1`.
      // Number of glasses that can be filled in the current level: `remainingTime / (filledLevels + 1)`.
      glassesCount + remainingTime / (filledLevels + 1)
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
    return TotalGlassesFilled(n, t);
}
// </vc-code>

