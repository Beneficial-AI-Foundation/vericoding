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
lemma CollisionTimeNonNegative(i: int, positions: seq<int>)
    requires 0 <= i < |positions|-1
    requires forall j :: 0 <= j < |positions| ==> positions[j] >= 0
    requires forall j, k :: 0 <= j < k < |positions| ==> positions[j] < positions[k]
    ensures CollisionTime(i, positions) >= 0
{
    assert positions[i+1] > positions[i];
    assert positions[i+1] - positions[i] >= 0;
}

lemma HasCollisionEquivalence(directions: string, positions: seq<int>, i: int)
    requires |directions| == |positions|
    requires 0 <= i <= |directions|-1
    ensures (exists j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L') <==>
            (exists j :: 0 <= j < |directions|-1 && directions[j] == 'R' && directions[j+1] == 'L' && j < i)
{
}

lemma MinimalCollisionTimeCorrectness(directions: string, positions: seq<int>, min_time: int, i: int)
    requires |directions| == |positions|
    requires 0 <= i <= |directions|-1
    requires exists j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' && CollisionTime(j, positions) == min_time
    requires forall j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' ==> CollisionTime(j, positions) >= min_time
    ensures exists j :: 0 <= j < |directions|-1 && directions[j] == 'R' && directions[j+1] == 'L' && CollisionTime(j, positions) == min_time
    ensures forall j :: 0 <= j < |directions|-1 && directions[j] == 'R' && directions[j+1] == 'L' && j < i ==> CollisionTime(j, positions) >= min_time
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
    var has_collision := false;
    var min_collision_time := 0;
    var found_first := false;
    
    for i := 0 to n-1
        invariant 0 <= i <= n-1
        invariant has_collision ==> found_first
        invariant found_first ==> has_collision
        invariant has_collision ==> min_collision_time >= 0
        invariant has_collision ==> (exists j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' && 
                                     CollisionTime(j, positions) == min_collision_time)
        invariant has_collision ==> (forall j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L' ==> 
                                     CollisionTime(j, positions) >= min_collision_time)
        invariant !has_collision ==> (forall j :: 0 <= j < i ==> !(directions[j] == 'R' && directions[j+1] == 'L'))
        invariant has_collision <==> (exists j :: 0 <= j < i && directions[j] == 'R' && directions[j+1] == 'L')
    {
        if directions[i] == 'R' && directions[i+1] == 'L' {
            var collision_time := CollisionTime(i, positions);
            CollisionTimeNonNegative(i, positions);
            
            if !found_first {
                min_collision_time := collision_time;
                found_first := true;
                has_collision := true;
            } else if collision_time < min_collision_time {
                min_collision_time := collision_time;
            }
        }
    }
    
    if has_collision {
        result := min_collision_time;
        
        HasCollisionEquivalence(directions, positions, n-1);
        MinimalCollisionTimeCorrectness(directions, positions, min_collision_time, n-1);
        
        assert has_collision <==> HasCollision(directions, positions);
        assert forall j :: 0 <= j < n-1 && directions[j] == 'R' && directions[j+1] == 'L' ==> 
                 CollisionTime(j, positions) >= min_collision_time;
        assert exists j :: 0 <= j < n-1 && directions[j] == 'R' && directions[j+1] == 'L' && 
                 CollisionTime(j, positions) == min_collision_time;
        assert IsMinimalCollisionTime(min_collision_time, directions, positions);
    } else {
        result := -1;
    }
}
// </vc-code>

