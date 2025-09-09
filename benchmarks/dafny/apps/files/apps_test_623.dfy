/*
Given two joysticks with initial charge levels a1 and a2 percent, determine the maximum number of minutes a game can last.
Each minute, exactly one joystick must be connected to a charger (gains 1% charge) while the other loses 2% charge.
Game continues while both joysticks have positive charge (> 0%). If a joystick has exactly 1% charge at the start of a minute,
it must be charged to avoid reaching 0%. Find the maximum number of minutes before at least one joystick reaches 0% charge.
*/

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
  assume {:axiom} false;
}
// </vc-code>
