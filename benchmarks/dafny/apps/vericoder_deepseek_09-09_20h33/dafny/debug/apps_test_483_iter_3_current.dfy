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
lemma MinLemma(collisionTimes: seq<int>, i: int)
    requires |collisionTimes| > 0
    requires 0 <= i < |collisionTimes|
    ensures (forall j :: 0 <= j < |collisionTimes| ==> collisionTimes[j] >= collisionTimes[i]) || exists j :: 0 <= j < |collisionTimes| && collisionTimes[j] < collisionTimes[i]
{
}

lemma ExistsMin(collisionTimes: seq<int>)
    requires |collisionTimes| > 0
    ensures exists m :: m in collisionTimes && (forall x :: x in collisionTimes ==> x >= m)
{
    if |collisionTimes| == 1 {
        // Trivial case: the only element is the minimum
    } else {
        var last := collisionTimes[|collisionTimes|-1];
        var prefix := collisionTimes[0..|collisionTimes|-1];
        ExistsMin(prefix);
        var m: int :| m in prefix && (forall x :: x in prefix ==> x >= m);
        if last < m {
            // The last element is smaller than the prefix minimum
            assert forall x :: x in collisionTimes ==> x >= last;
            assert last in collisionTimes;
        } else {
            // The prefix minimum is still the overall minimum
            assert forall x :: x in collisionTimes ==> x >= m;
            assert m in collisionTimes;
        }
    }
}

lemma ForallConcat<T>(s1: seq<T>, s2: seq<T>, P: T -> bool)
    requires forall x :: x in s1 ==> P(x)
    requires forall x :: x in s2 ==> P(x)
    ensures forall x :: x in s1 + s2 ==> P(x)
{
}

lemma CollisionTimeNonNegative(positions: seq<int>, i: int)
    requires |positions| >= 2
    requires 0 <= i < |positions|-1
    requires (forall k :: 0 <= k < |positions| ==> positions[k] >= 0)
    requires (forall k, j :: 0 <= k < j < |positions| ==> positions[k] < positions[j])
    ensures CollisionTime(i, positions) >= 0
{
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
    var hasCollision := false;
    var minTime := -1;
    
    var i := 0;
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant !hasCollision ==> (forall j :: 0 <= j < i ==> !(directions[j] == 'R' && directions[j+1] == 'L'))
        invariant hasCollision ==> (exists j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' && minTime == CollisionTime(j, positions))
        invariant hasCollision ==> (forall j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' ==> CollisionTime(j, positions) >= minTime)
        invariant minTime >= 0 || minTime == -1
    {
        if directions[i] == 'R' && directions[i+1] == 'L' {
            var currentTime := CollisionTime(i, positions);
            CollisionTimeNonNegative(positions, i);
            assert currentTime >= 0;
            
            if !hasCollision {
                hasCollision := true;
                minTime := currentTime;
                assert minTime >= 0;
                assert exists j :: 0 <= j < i+1 && directions[j] == 'R' && directions[j+1] == 'L' && minTime == CollisionTime(j, positions);
                assert forall j :: 0 <= j < i+1 && directions[j] == 'R' && directions[j+1] == 'L' ==> CollisionTime(j, positions) >= minTime;
            } else {
                if currentTime < minTime {
                    minTime := currentTime;
                } else {
                    minTime := minTime;
                }
                assert minTime >= 0;
                assert forall j :: 0 <= j < i+1 && directions[j] == 'R' && directions[j+1] == 'L' ==> CollisionTime(j, positions) >= minTime;
            }
        } else {
            if hasCollision {
                assert forall j :: 0 <= j < i+1 && directions[j] == 'R' && directions[j+1] == 'L' ==> CollisionTime(j, positions) >= minTime;
            }
        }
        i := i + 1;
    }
    
    if hasCollision {
        result := minTime;
        assert exists j :: 0 <= j < n-1 && directions[j] == 'R' && directions[j+1] == 'L' && minTime == CollisionTime(j, positions);
        assert forall j :: 0 <= j < n-1 && directions[j] == 'R' && directions[j+1] == 'L' ==> CollisionTime(j, positions) >= minTime;
    } else {
        result := -1;
    }
}
// </vc-code>

