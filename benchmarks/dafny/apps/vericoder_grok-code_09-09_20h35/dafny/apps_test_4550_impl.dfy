predicate ValidInputFormat(input: string)
{
    |input| > 0 && 
    var nums := ExtractNumbers(input, 0, [], "");
    |nums| >= 3 && 
    (forall i :: 0 <= i < 3 ==> 1 <= nums[i] <= 100)
}

function ParseThreeIntsFunc(input: string): (int, int, int)
    requires |input| > 0
    requires ValidInputFormat(input)
    ensures ParseThreeIntsFunc(input).0 >= 1 && ParseThreeIntsFunc(input).1 >= 1 && ParseThreeIntsFunc(input).2 >= 1
    ensures ParseThreeIntsFunc(input).0 <= 100 && ParseThreeIntsFunc(input).1 <= 100 && ParseThreeIntsFunc(input).2 <= 100
{
    var nums := ExtractNumbers(input, 0, [], "");
    (nums[0], nums[1], nums[2])
}

predicate CanDistributeEqually(a: int, b: int, c: int)
{
    a + b == c || b + c == a || c + a == b
}

// <vc-helpers>
function parseInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 0 then 0
  else (s[|s|-1] - '0') + parseInt(s[..|s|-1]) * 10
}

function ExtractNumbers(input: string, index: nat, nums: seq<int>, current: string): seq<int>
  decreases |input| - index
{
  if index >= |input| then
    if |current| > 0 then
      nums + [parseInt(current)]
    else
      nums
  else
    var ch := input[index];
    if '0' <= ch <= '9' then
      ExtractNumbers(input, index + 1, nums, current + [ch])
    else if ch == ' ' || ch == '\n' || ch == '\t' /* assuming separators */ then
      if |current| > 0 then
        ExtractNumbers(input, index + 1, nums + [parseInt(current)], "")
      else
        ExtractNumbers(input, index + 1, nums, "")
    else
      ExtractNumbers(input, index + 1, nums, current) // ignore other chars
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInputFormat(input)
    ensures result == "Yes\n" || result == "No\n"
    ensures var numbers := ParseThreeIntsFunc(input);
            var a := numbers.0;
            var b := numbers.1; 
            var c := numbers.2;
            result == "Yes\n" <==> CanDistributeEqually(a, b, c)
    ensures var numbers := ParseThreeIntsFunc(input);
            numbers.0 >= 1 && numbers.1 >= 1 && numbers.2 >= 1 &&
            numbers.0 <= 100 && numbers.1 <= 100 && numbers.2 <= 100
// </vc-spec>
// <vc-code>
{
  var numbers := ParseThreeIntsFunc(input);
  var a := numbers.0;
  var b := numbers.1;
  var c := numbers.2;
  if CanDistributeEqually(a, b, c) {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
}
// </vc-code>

