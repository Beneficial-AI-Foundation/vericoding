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
lemma ValidMinutesNonnegative(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures CountValidMinutes(a, b) >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 {
        // Base case returns 0
    } else if a == 1 && b == 1 {
        // Base case returns 0
    } else {
        var new_a := if a < b then a + 1 else a - 2;
        var new_b := if a < b then b - 2 else b + 1;
        // Prove new arguments are non-negative
        if a < b {
            // Since a < b, a >= 1 > 0 => a+1 >= 2 > 0
            // b >= a+1 >= 2 (since a < b and integers) => b-2 >= 0
        } else {
            // a >= b and (a,b) != (1,1) => a >= 2 (if a==1 then b<=1 => (1,1) excluded)
            // a >= 2 => a-2 >= 0
            // b >= 1 => b+1 >= 2 > 0
        }
        // Recursive call measure: new_a + new_b = (a+b) - 1 < a+b
        ValidMinutesNonnegative(new_a, new_b);
        // Result is (0 or 1) + non-negative recursive result => non-negative
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
    ValidMinutesNonnegative(a1, a2);
    return CountValidMinutes(a1, a2);
}
// </vc-code>

