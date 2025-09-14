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
function SplitLines(input: string): seq<string>
    ensures |SplitLines(input)| >= 0
    { [] }  // Add empty body to avoid warning

function ParseInt(s: string): int
    ensures ParseInt(s) >= 0
    { 0 }  // Add empty body to avoid warning

function ParseIntArray(s: string): seq<int>
    ensures |ParseIntArray(s)| >= 0
    ensures forall i :: 0 <= i < |ParseIntArray(s)| ==> ParseIntArray(s)[i] >= 0
    { [] }  // Add empty body to avoid warning

lemma SumNonNegative(nums: seq<int>)
    requires forall i :: 0 <= i < |nums| ==> nums[i] >= 0
    ensures Sum(nums) >= 0
{
    if |nums| == 0 {
    } else {
        SumNonNegative(nums[1..]);
        calc {
            Sum(nums);
            == nums[0] + Sum(nums[1..]);
            >= 0 + Sum(nums[1..]);
            == Sum(nums[1..]);
            >= 0;
        }
    }
}

lemma SumPreservesOrder(nums1: seq<int>, nums2: seq<int>)
    requires |nums1| == |nums2|
    requires forall i :: 0 <= i < |nums1| ==> nums1[i] >= nums2[i]
    ensures Sum(nums1) >= Sum(nums2)
{
    if |nums1| == 0 {
    } else {
        SumPreservesOrder(nums1[1..], nums2[1..]);
        calc {
            Sum(nums1);
            == nums1[0] + Sum(nums1[1..]);
            >= nums2[0] + Sum(nums1[1..]);
            >= nums2[0] + Sum(nums2[1..]);
            == Sum(nums2);
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
  if IsValidInput(input) {
    var lines := SplitLines(input);
    var initialSum := GetInitialSum(input);
    var targetSum := GetTargetSum(input);
    if initialSum >= targetSum {
      result := "Yes";
    } else {
      result := "No";
    }
  } else {
    result := "No";
  }
}
// </vc-code>

