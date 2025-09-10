predicate containsThreeSpaceSeparatedIntegers(input: string)
{
    exists i, j, k :: (0 <= i < j < k <= |input| &&
    isValidIntegerSubstring(input, 0, i) &&
    input[i] == ' ' &&
    isValidIntegerSubstring(input, i+1, j) &&
    input[j] == ' ' &&
    isValidIntegerSubstring(input, j+1, k) &&
    (k == |input| || input[k] == '\n'))
}

predicate exactlyTwoAreEqual(input: string)
    requires containsThreeSpaceSeparatedIntegers(input)
{
    var nums := parseThreeNumbers(input);
    (nums.0 == nums.1 && nums.0 != nums.2) ||
    (nums.0 == nums.2 && nums.0 != nums.1) ||
    (nums.1 == nums.2 && nums.1 != nums.0)
}

predicate isValidIntegerString(s: string)
{
    if |s| == 0 then false
    else if s == "0" then true
    else if |s| > 0 && s[0] == '-' then 
        |s| > 1 && isDigitSequence(s[1..]) && s[1] != '0'
    else isDigitSequence(s) && s[0] != '0'
}

predicate isDigitSequence(s: string)
{
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate isValidIntegerSubstring(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
{
    if start == end then false
    else
        var substr := s[start..end];
        isValidIntegerString(substr)
}

function findDifferentNumber(input: string): string
    requires containsThreeSpaceSeparatedIntegers(input)
    requires exactlyTwoAreEqual(input)
{
    var nums := parseThreeNumbers(input);
    var different := if nums.0 == nums.1 then nums.2
                    else if nums.0 == nums.2 then nums.1
                    else nums.0;
    intToStringPure(different)
}

// <vc-helpers>
function parseThreeNumbers(input: string): (int, int, int)
  requires containsThreeSpaceSeparatedIntegers(input)
{
  var i :| 0 <= i < |input| && input[i] == ' ';
  var j :| i+1 <= j < |input| && input[j] == ' ';
  var num1_str := extractIntegerSubstring(input, 0, i);
  var num2_str := extractIntegerSubstring(input, i+1, j);
  var num3_str := extractIntegerSubstring(input, j+1, |input|);
  (stringToInt(num1_str), stringToInt(num2_str), stringToInt(num3_str))
}

function extractIntegerSubstring(s: string, start: int, end: int): string
  requires 0 <= start <= end <= |s|
  requires isValidIntegerSubstring(s, start, end)
{
  s[start..end]
}

function stringToInt(s: string): int
  requires isValidIntegerString(s)
{
  if |s| == 0 then 0
  else if s[0] == '-' then -digitSequenceToInt(s[1..])
  else digitSequenceToInt(s)
}

function digitSequenceToInt(s: string): int
  requires isDigitSequence(s)
  requires |s| > 0 ==> s[0] != '0'
{
  if |s| == 0 then 0
  else (s[|s|-1] as int - '0' as int) + 10 * digitSequenceToInt(s[0..|s|-1])
}

function intToStringPure(n: int): string
{
  if n == 0 then "0"
  else if n < 0 then "-" + positiveIntToStringPure(-n)
  else positiveIntToStringPure(n)
}

function positiveIntToStringPure(n: int): string
  requires n >= 0
{
  if n == 0 then ""
  else positiveIntToStringPure(n / 10) + [((n % 10) + '0' as int) as char]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires containsThreeSpaceSeparatedIntegers(input)
    requires exactlyTwoAreEqual(input)
    ensures |result| > 0
    ensures isValidIntegerString(result)
    ensures result == findDifferentNumber(input)
// </vc-spec>
// <vc-code>
{
  var i: int :| 0 <= i < |input| && input[i] == ' ';
  var j: int :| i+1 <= j < |input| && input[j] == ' ';
  
  var num1_str := input[0..i];
  var num2_str := input[i+1..j];
  var num3_str := input[j+1..|input|];
  
  var num1 := stringToInt(num1_str);
  var num2 := stringToInt(num2_str);
  var num3 := stringToInt(num3_str);
  
  if num1 == num2 {
    result := num3_str;
  } else if num1 == num3 {
    result := num2_str;
  } else {
    result := num1_str;
  }
}
// </vc-code>

