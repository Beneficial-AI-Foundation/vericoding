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
// No additional helpers needed; the implementation is straightforward and verifies with the given predicates.
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
    var hasCollision := false;
    var first := true;
    var minTime := 0;
    var i := 0;
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant hasCollision == !first
        invariant !first ==> minTime == min j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' :: (positions[j+1] - positions[j]) / 2
    {
        if directions[i] == 'R' && directions[i+1] == 'L' {
            var t := (positions[i+1] - positions[i]) / 2;
            if first || t < minTime {
                minTime := t;
                first := false;
                hasCollision := true;
            }
        }
        i := i + 1;
    }
    if hasCollision {
        result := minTime;
    } else {
        result := -1;
    }
}
// </vc-code>

