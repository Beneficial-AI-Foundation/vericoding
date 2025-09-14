predicate ValidInput(n: int, directions: string, positions: seq<int>)
{
    n >= 1 &&
    |directions| == n &&
    |positions| == n &&
    (forall i :: 0 <= i < n ==> directions[i] == 'R' || directions[i] == 'L') &&
    (forall i :: 0 <= i < n ==> positions[i] % 2 == 0 && positions[i] >= 0) &&
    (forall i, j :: 0 <= i < j < n ==> positions[i] < positions[j])
}

predicate HasCollision(directions: string, positions: seq<int>)
    requires |directions| == |positions|
{
    exists i :: 0 <= i < |directions|-1 && directions[i] == 'R' && directions[i+1] == 'L'
}

function CollisionTime(i: int, positions: seq<int>): int
    requires 0 <= i < |positions|-1
{
    (positions[i+1] - positions[i]) / 2
}

predicate IsMinimalCollisionTime(result: int, directions: string, positions: seq<int>)
    requires |directions| == |positions|
{
    (forall i :: 0 <= i < |directions|-1 && directions[i] == 'R' && directions[i+1] == 'L' ==> 
        CollisionTime(i, positions) >= result) &&
    (exists i :: 0 <= i < |directions|-1 && directions[i] == 'R' && directions[i+1] == 'L' && 
        CollisionTime(i, positions) == result)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, directions: string, positions: seq<int>) returns (result: int)
    requires ValidInput(n, directions, positions)
    ensures result == -1 || result >= 0
    ensures result != -1 ==> HasCollision(directions, positions)
    ensures result == -1 ==> !HasCollision(directions, positions)
    ensures result != -1 ==> IsMinimalCollisionTime(result, directions, positions)
// </vc-spec>
// <vc-code>
{
  var have := false;
  var min := 0;
  var minIndex := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |directions| == n && |positions| == n
    invariant have ==> 0 <= minIndex < i
    invariant have ==> directions[minIndex] == 'R' && directions[minIndex + 1] == 'L'
    invariant have ==> min == CollisionTime(minIndex, positions)
    invariant have ==> 0 <= min
    invariant (forall j :: 0 <= j < i && directions[j] == 'R' && directions[j + 1] == 'L' ==> CollisionTime(j, positions) >= min)
    invariant have <==> (exists j :: 0 <= j < i && directions[j] == 'R' && directions[j + 1] == 'L')
    decreases n - i
  {
    if directions[i] == 'R' && directions[i + 1] == 'L' {
      var t := CollisionTime(i, positions);
      if !have || t < min {
        min := t;
        minIndex := i;
        have := true;
      }
    }
    i := i + 1;
  }
  if have {
    result := min;
  } else {
    result := -1;
  }
}
// </vc-code>

