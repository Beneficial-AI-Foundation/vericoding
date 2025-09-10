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
lemma SumNonNegativeForNonNegativeSeq(nums: seq<int>)
    requires forall i :: 0 <= i < |nums| ==> nums[i] >= 0
    ensures Sum(nums) >= 0
    decreases |nums|
{
    if |nums| == 0 {
        // Base case: empty sequence has sum 0
    } else {
        // Inductive case
        SumNonNegativeForNonNegativeSeq(nums[1..]);
    }
}

lemma SumDistributive(a: seq<int>, b: seq<int>)
    ensures Sum(a + b) == Sum(a) + Sum(b)
    decreases |a|
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        assert a + b == [a[0]] + (a[1..] + b);
        SumDistributive(a[1..], b);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures result == "Yes" || result == "No"
    ensures IsValidInput(input) ==> 
        (result == "Yes" <==> GetInitialSum(input) >= GetTargetSum(input))
    ensures !IsValidInput(input) ==> result == "No"
// </vc-spec>
// <vc-code>
{
    if !IsValidInput(input) {
        return "No";
    }
    
    var initialSum := GetInitialSum(input);
    var targetSum := GetTargetSum(input);
    
    if initialSum >= targetSum {
        return "Yes";
    } else {
        return "No";
    }
}
// </vc-code>

