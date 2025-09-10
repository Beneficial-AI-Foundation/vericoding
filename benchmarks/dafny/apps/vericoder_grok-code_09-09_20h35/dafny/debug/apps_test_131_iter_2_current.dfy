predicate IsValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && 
    ParseInt(lines[0]) > 0 &&
    |ParseIntArray(lines[1])| == ParseInt(lines[0]) &&
    |ParseIntArray(lines[2])| == ParseInt(lines[0])
}

function GetInitialSum(input: string): int
    requires IsValidInput(input)
{
    var lines := SplitLines(input);
    Sum(ParseIntArray(lines[1]))
}

function GetTargetSum(input: string): int
    requires IsValidInput(input)
{
    var lines := SplitLines(input);
    Sum(ParseIntArray(lines[2]))
}

function Sum(nums: seq<int>): int
    decreases |nums|
{
    if |nums| == 0 then 0
    else nums[0] + Sum(nums[1..])
}

// <vc-helpers>
function {:opaque} SplitLines(input: string): seq<string>
function {:opaque} ParseInt(s: string): int
function {:opaque} ParseIntArray(s: string): seq<int>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures result == "Yes" || result == "No"
    ensures IsValidInput(input) ==> 
        (result == "Yes" <==> GetInitialSum(input) >= GetTargetSum(input))
    ensures !IsValidInput(input) ==> result == "No"
// </vc-spec>
// <vc-code>
if !IsValidInput(input) {
        result := "No";
    } else {
        var sum1 := GetInitialSum(input);
        var sum2 := GetTargetSum(input);
        if sum1 >= sum2 {
            result := "Yes";
        } else {
            result := "No";
        }
    }
// </vc-code>

