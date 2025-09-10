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
function TotalGlassesFilled(n: int, t: int): int
  requires ValidInput(n, t)
  ensures 0 <= TotalGlassesFilled(n, t) <= TotalGlasses(n)
{
  if t == 0 then 0
  else if n == 1 then min(1, t) // If n=1, only 1 glass needed, it's either filled or not.
  else
    var filledLevels := 0;
    var remainingTime := t;
    var glassesCount := 0;

    while filledLevels < n && remainingTime >= (filledLevels + 1) * (filledLevels + 1)
      decreases n - filledLevels
      invariant 0 <= filledLevels <= n
      invariant remainingTime >= 0
      invariant (filledLevels == 0 && glassesCount == 0) || (filledLevels > 0 && glassesCount == TotalGlasses(filledLevels))
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
    // Note: integer division automatically floors, which is what we need here.
    glassesCount + (if (filledLevels + 1) > 0 then remainingTime / (filledLevels + 1) else 0)
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

