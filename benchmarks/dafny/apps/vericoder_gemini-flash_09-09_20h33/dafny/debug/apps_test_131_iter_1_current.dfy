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
{
  input.Split('\n')
}

function ParseInt(s: string): int
{
  var num := 0;
  var i := 0;
  var negative := false;

  if |s| > 0 && s[0] == '-' {
    negative := true;
    i := 1;
  }

  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9' || (k==0 && s[0]=='-')
    invariant num >= 0
    invariant num == (if negative then -1 else 1) * ParseIntPortion(s, (if negative then 1 else 0), i)
  {
    if '0' <= s[i] <= '9' {
      num := num * 10 + (s[i] as int - '0' as int);
    }
    i := i + 1;
  }
  if negative then -num else num
}

function ParseIntPortion(s: string, start: int, end: int): int
  requires 0 <= start <= end <= |s|
  requires forall k :: start <= k < end ==> '0' <= s[k] <= '9'
{
  if start == end then 0
  else ParseIntPortion(s, start, end - 1) * 10 + (s[end - 1] as int - '0' as int)
}

function ParseIntArray(s: string): seq<int>
{
  if |s| == 0 then []
  else s.Split(' ').Map(x => ParseInt(x))
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
        var initialSum := GetInitialSum(input);
        var targetSum := GetTargetSum(input);
        if initialSum >= targetSum then {
            result := "Yes";
        } else {
            result := "No";
        }
    } else {
        result := "No";
    }
}
// </vc-code>

