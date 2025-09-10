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
function min(a: int, b: int): int
    requires a >= 0 || a == -1
    requires b >= 0 || b == -1
    ensures (a == -1 || b == -1) && (a != -1 || b != -1) ==> (result >= 0 || result == -1)
    ensures a != -1 && b != -1 ==> result >= 0
    ensures a == -1 && b == -1 ==> result == -1
{
    if a == -1 then b
    else if b == -1 then a
    else if a < b then a else b
}
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
    var minCollisionTime: int := -1;
    var foundCollision: bool := false;

    for i := 0 to n - 2
        invariant 0 <= i <= n - 1
        invariant (forall k :: 0 <= k < i && directions[k] == 'R' && directions[k+1] == 'L' ==> 
            (minCollisionTime == -1 || CollisionTime(k, positions) >= minCollisionTime))
        invariant foundCollision == (exists k :: 0 <= k < i && directions[k] == 'R' && directions[k+1] == 'L')
        invariant foundCollision ==> minCollisionTime >= 0
        invariant (foundCollision && minCollisionTime != -1) ==> (exists k :: 0 <= k < i && directions[k] == 'R' && directions[k+1] == 'L' && CollisionTime(k, positions) == minCollisionTime)

    {
        if directions[i] == 'R' && directions[i+1] == 'L' {
            var currentCollisionTime := CollisionTime(i, positions);
            if !foundCollision || currentCollisionTime < minCollisionTime {
                minCollisionTime := currentCollisionTime;
                foundCollision := true;
            }
        }
    }

    result := minCollisionTime;
    if !foundCollision {
        result := -1;
    }
}
// </vc-code>

