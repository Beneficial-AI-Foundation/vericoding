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
function charToDigit(c: char): int
  requires '0' <= c <= '9'
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else 9
}

function digitToString(d: int): string
  requires 0 <= d < 10
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else "9"
}

function pow10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

function stringToNat(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 1 then charToDigit(s[0])
  else charToDigit(s[0]) * pow10(|s| - 1) + stringToNat(s[1..])
}

function substringToInt(s: string, start: int, end: int): int
  requires 0 <= start < end <= |s|
  requires isValidIntegerSubstring(s, start, end)
  decreases end - start
{
  var substr := s[start..end];
  if substr[0] == '-' then -stringToNat(substr[1..]) else stringToNat(substr)
}

function parseThreeNumbers(input: string): (int, int, int)
  requires containsThreeSpaceSeparatedIntegers(input)
{
  var i, j, k :| 0 <= i < j < k <= |input| &&
               isValidIntegerSubstring(input, 0, i) &&
               input[i] == ' ' &&
               isValidIntegerSubstring(input, i + 1, j) &&
               input[j] == ' ' &&
               isValidIntegerSubstring(input, j + 1, k) &&
               (k == |input| || input[k] == '\n');
  (substringToInt(input, 0, i), substringToInt(input, i + 1, j), substringToInt(input, j + 1, k))
}

function natToString(n: int): string
  requires n >= 0
  decreases n
{
  if n < 10 then digitToString(n)
  else natToString(n / 10) + digitToString(n % 10)
}

function intToStringPure(x: int): string
{
  if x == 0 then "0"
  else if x < 0 then "-" + natToString(-x)
  else natToString(x)
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
  result := findDifferentNumber(input);
}
// </vc-code>

