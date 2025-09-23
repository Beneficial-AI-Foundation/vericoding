// <vc-preamble>

predicate ValidInput(n: int, lengths: seq<int>, terrain: string)
{
  n >= 1 &&
  |lengths| == n &&
  |terrain| == n &&
  n <= 100000 &&
  (forall i :: 0 <= i < n ==> lengths[i] >= 1) &&
  (forall i :: 0 <= i < n ==> lengths[i] <= 1000000000000) &&
  (forall i :: 0 <= i < n ==> terrain[i] in {'G', 'W', 'L'}) &&
  terrain[0] != 'L'
}

ghost function computeMinimumTime(n: int, lengths: seq<int>, terrain: string): int
  requires ValidInput(n, lengths, terrain)
{
  computeTimeRec(n, lengths, terrain, 0, 0, 0, 0, false)
}

ghost function computeTimeRec(n: int, lengths: seq<int>, terrain: string, pos: int, water: int, grass: int, cgrass: int, seen: bool): int
  requires n >= 1
  requires |lengths| == n  
  requires |terrain| == n
  requires 0 <= pos <= n
  requires water >= 0 && grass >= 0 && cgrass >= 0
  requires forall i :: 0 <= i < n ==> lengths[i] >= 1
  requires forall i :: 0 <= i < n ==> terrain[i] in {'G', 'W', 'L'}
  decreases n - pos
{
  if pos == n then 0
  else if terrain[pos] == 'G' then
    var dist := lengths[pos];
    if water >= dist then
      2 * dist + computeTimeRec(n, lengths, terrain, pos + 1, water - dist, grass, cgrass + dist, seen)
    else
      2 * water + 3 * (dist - water) + computeTimeRec(n, lengths, terrain, pos + 1, 0, grass + (dist - water), cgrass + water, seen)
  else if terrain[pos] == 'W' then
    2 * lengths[pos] + computeTimeRec(n, lengths, terrain, pos + 1, water + lengths[pos], grass, cgrass, true)
  else // terrain[pos] == 'L'
    var dist := lengths[pos];
    if water >= dist then
      2 * dist + computeTimeRec(n, lengths, terrain, pos + 1, water - dist, grass, cgrass, seen)
    else
      var remaining := dist - water;
      var baseTime := 2 * water;
      if cgrass >= remaining then
        baseTime + 3 * remaining + computeTimeRec(n, lengths, terrain, pos + 1, 0, grass + remaining, cgrass - remaining, seen)
      else
        var afterCgrass := remaining - cgrass;
        var time1 := baseTime + 3 * cgrass;
        if grass >= afterCgrass then
          time1 + 3 * afterCgrass + computeTimeRec(n, lengths, terrain, pos + 1, 0, grass - afterCgrass, 0, seen)
        else
          var final := afterCgrass - grass;
          var time2 := time1 + 3 * grass;
          var penalty := if seen then 4 * final else 6 * final;
          time2 + penalty + computeTimeRec(n, lengths, terrain, pos + 1, 0, 0, 0, seen)
}

ghost function sumLengths(lengths: seq<int>): int
{
  if |lengths| == 0 then 0 else lengths[0] + sumLengths(lengths[1..])
}

ghost function hasWater(terrain: string): bool
{
  exists i :: 0 <= i < |terrain| && terrain[i] == 'W'
}

ghost function minPossibleTime(n: int, lengths: seq<int>, terrain: string): int
  requires ValidInput(n, lengths, terrain)
{
  if terrain[0] == 'W' then 2 * lengths[0] + 2 * sumLengths(lengths[1..])
  else 3 * lengths[0] + 2 * sumLengths(lengths[1..])
}

ghost function maxPossibleTime(n: int, lengths: seq<int>, terrain: string): int
  requires ValidInput(n, lengths, terrain)
{
  if hasWater(terrain) then 4 * sumLengths(lengths)
  else 6 * sumLengths(lengths)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, lengths: seq<int>, terrain: string) returns (result: int)
  requires ValidInput(n, lengths, terrain)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var water := 0;
  var grass := 0;
  var cgrass := 0;
  var time := 0;
  var seen := false;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant water >= 0
    invariant grass >= 0
    invariant cgrass >= 0
    invariant time >= 0
    invariant seen ==> exists j :: 0 <= j < i && terrain[j] == 'W'
  {
    if terrain[i] == 'G' {
      var dist := lengths[i];
      if water >= dist {
        water := water - dist;
        time := time + 2 * dist;
        cgrass := cgrass + dist;
      } else {
        dist := dist - water;
        time := time + 2 * water;
        cgrass := cgrass + water;
        water := 0;
        time := time + 3 * dist;
        grass := grass + dist;
      }
    } else if terrain[i] == 'W' {
      water := water + lengths[i];
      time := time + 2 * lengths[i];
      seen := true;
    } else { // terrain[i] == 'L'
      var dist := lengths[i];
      if water >= dist {
        water := water - dist;
        time := time + 2 * dist;
      } else {
        dist := dist - water;
        time := time + 2 * water;
        water := 0;
        if cgrass >= dist {
          cgrass := cgrass - dist;
          grass := grass + dist;
          time := time + 3 * dist;
        } else {
          dist := dist - cgrass;
          grass := grass + cgrass;
          time := time + 3 * cgrass;
          cgrass := 0;
          if grass >= dist {
            grass := grass - dist;
            time := time + 3 * dist;
          } else {
            dist := dist - grass;
            time := time + 3 * grass;
            grass := 0;
            if seen {
              time := time + 4 * dist;
            } else {
              time := time + 6 * dist;
            }
          }
        }
      }
    }
    i := i + 1;
  }

  result := time;
}
// </vc-code>
