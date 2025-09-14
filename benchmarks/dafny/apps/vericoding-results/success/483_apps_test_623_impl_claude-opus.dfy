function CountValidMinutes(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 then 0
    else if a == 1 && b == 1 then 0
    else (if a > 1 || b > 1 then 1 else 0) + 
         CountValidMinutes(if a < b then a + 1 else a - 2, if a < b then b - 2 else b + 1)
}

// <vc-helpers>
lemma CountValidMinutesNonNegative(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures CountValidMinutes(a, b) >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 {
        assert CountValidMinutes(a, b) == 0;
    } else if a == 1 && b == 1 {
        assert CountValidMinutes(a, b) == 0;
    } else {
        var nextA := if a < b then a + 1 else a - 2;
        var nextB := if a < b then b - 2 else b + 1;
        CountValidMinutesNonNegative(nextA, nextB);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a1: int, a2: int) returns (result: int)
    requires a1 >= 1 && a2 >= 1
    ensures result >= 0
    ensures result == CountValidMinutes(a1, a2)
    ensures (a1 == 1 && a2 == 1) ==> result == 0
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var currentA := a1;
    var currentB := a2;
    
    while currentA > 0 && currentB > 0
        invariant currentA >= 0 && currentB >= 0
        invariant count >= 0
        invariant count + CountValidMinutes(currentA, currentB) == CountValidMinutes(a1, a2)
        decreases currentA + currentB
    {
        if currentA == 1 && currentB == 1 {
            break;
        }
        
        count := count + 1;
        
        var nextA := if currentA < currentB then currentA + 1 else currentA - 2;
        var nextB := if currentA < currentB then currentB - 2 else currentB + 1;
        
        currentA := nextA;
        currentB := nextB;
    }
    
    result := count;
}
// </vc-code>

