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
lemma CountValidMinutesLemma(a: int, b: int)
    requires a >= 0 && b >= 0
    decreases a + b
    ensures CountValidMinutes(a, b) >= 0
{
    if a <= 0 || b <= 0 {
        // Base case: already 0
    } else if a == 1 && b == 1 {
        // Base case: already 0
    } else {
        CountValidMinutesLemma(if a < b then a + 1 else a - 2, if a < b then b - 2 else b + 1);
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
    result := 0;
    var x := a1;
    var y := a2;
    
    while x >= 1 && y >= 1 && !(x == 1 && y == 1)
        invariant x >= 0 && y >= 0
        invariant result >= 0
        invariant result + CountValidMinutes(x, y) == CountValidMinutes(a1, a2)
        decreases x + y
    {
        result := result + 1;
        if x < y {
            x := x + 1;
            y := y - 2;
        } else {
            x := x - 2;
            y := y + 1;
        }
    }
}
// </vc-code>

