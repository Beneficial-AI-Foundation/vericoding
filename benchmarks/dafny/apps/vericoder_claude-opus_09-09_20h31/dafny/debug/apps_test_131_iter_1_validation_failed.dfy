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
// Assume these parsing functions exist
function SplitLines(s: string): seq<string>

function ParseInt(s: string): int

function ParseIntArray(s: string): seq<int>

// Helper lemma to compute sum iteratively
lemma SumComputation(nums: seq<int>) returns (s: int)
    ensures s == Sum(nums)
{
    s := 0;
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant s == Sum(nums[..i])
    {
        assert nums[..i+1] == nums[..i] + [nums[i]];
        SumExtension(nums[..i], nums[i]);
        s := s + nums[i];
        i := i + 1;
    }
    assert nums[..|nums|] == nums;
}

// Helper lemma for sum extension
lemma SumExtension(s: seq<int>, x: int)
    ensures Sum(s + [x]) == Sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert Sum([x]) == x + Sum([]);
        assert Sum([]) == 0;
    } else {
        calc {
            Sum(s + [x]);
            == { assert (s + [x])[0] == s[0]; assert (s + [x])[1..] == s[1..] + [x]; }
            s[0] + Sum(s[1..] + [x]);
            == { SumExtension(s[1..], x); }
            s[0] + Sum(s[1..]) + x;
            == 
            Sum(s) + x;
        }
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
    
    var lines := SplitLines(input);
    var n := ParseInt(lines[0]);
    var initialArray := ParseIntArray(lines[1]);
    var targetArray := ParseIntArray(lines[2]);
    
    var initialSum := SumComputation(initialArray);
    var targetSum := SumComputation(targetArray);
    
    if initialSum >= targetSum {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

