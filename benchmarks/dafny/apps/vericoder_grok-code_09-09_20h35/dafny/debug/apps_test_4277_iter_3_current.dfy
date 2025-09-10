predicate ValidInput(n: int, a: int, b: int)
{
    1 <= n <= 20 && 1 <= a <= 50 && 1 <= b <= 50
}

function TrainCost(n: int, a: int): int
{
    n * a
}

function MinimumCost(n: int, a: int, b: int): int
{
    var trainCost := TrainCost(n, a);
    if trainCost < b then trainCost else b
}

predicate CorrectResult(input: string, result: string)
{
    var lines := SplitString(input, '\n');
    if |lines| > 0 then
        var parts := SplitString(lines[0], ' ');
        if |parts| >= 3 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2]) then
            var n := StringToInt(parts[0]);
            var a := StringToInt(parts[1]);
            var b := StringToInt(parts[2]);
            ValidInput(n, a, b) ==> result == IntToString(MinimumCost(n, a, b)) + "\n"
        else
            result == ""
    else
        result == ""
}

// <vc-helpers>
// Empty or auxiliary lemmas if needed, but here none required as the fix is in the method body.
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures CorrectResult(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitString(input, '\n');
    if |lines| == 0 then {
        result := "";
    } else {
        var parts := SplitString(lines[0], ' ');
        if |parts| < 3 then 
            result := "";
        else {
            var s_n := parts[0];
            if !IsValidInteger(s_n) then 
                result := "";
            else {
                var n := StringToInt(s_n);
                var s_a := parts[1];
                if !IsValidInteger(s_a) then 
                    result := "";
                else {
                    var a := StringToInt(s_a);
                    var s_b := parts[2];
                    if !IsValidInteger(s_b) then 
                        result := "";
                    else {
                        var b := StringToInt(s_b);
                        if !ValidInput(n, a, b) then 
                            result := "";
                        else {
                            var cost := MinimumCost(n, a, b);
                            result := IntToString(cost) + "\n";
                        }
                    }
                }
            }
        }
    }
}
// </vc-code>

