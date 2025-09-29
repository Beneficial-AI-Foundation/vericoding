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
lemma CollisionTimePositive(i: int, positions: seq<int>)
    requires 0 <= i < |positions|-1
    requires forall j, k :: 0 <= j < k < |positions| ==> positions[j] < positions[k]
    requires forall j :: 0 <= j < |positions| ==> positions[j] % 2 == 0
    ensures CollisionTime(i, positions) > 0
{
    assert positions[i] < positions[i+1];
    assert positions[i] % 2 == 0;
    assert positions[i+1] % 2 == 0;
    // Since both are even and positions[i] < positions[i+1], the difference is at least 2
    assert positions[i+1] - positions[i] >= 2;
    assert (positions[i+1] - positions[i]) / 2 >= 1;
    assert CollisionTime(i, positions) >= 1;
    assert CollisionTime(i, positions) > 0;
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
    var minTime := -1;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant minTime == -1 || minTime >= 0
        invariant minTime != -1 ==> exists j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L'
        invariant minTime != -1 ==> forall j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' ==> CollisionTime(j, positions) >= minTime
        invariant minTime != -1 ==> exists j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' && CollisionTime(j, positions) == minTime
        invariant minTime == -1 ==> forall j :: 0 <= j < i ==> !(directions[j] == 'R' && directions[j+1] == 'L')
    {
        if directions[i] == 'R' && directions[i+1] == 'L' {
            var collTime := CollisionTime(i, positions);
            if minTime == -1 || collTime < minTime {
                minTime := collTime;
            }
        }
        i := i + 1;
    }
    
    result := minTime;
}
// </vc-code>

