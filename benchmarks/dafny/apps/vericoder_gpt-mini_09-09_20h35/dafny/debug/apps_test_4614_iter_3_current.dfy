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

// Deterministic parsing helpers to avoid non-unique let-such-that
function firstI(input: string, pos: int): int
  requires containsThreeSpaceSeparatedIntegers(input)
  requires 1 <= pos <= |input| - 1
  decreases |input| - pos
{
  if input[pos] == ' ' && isValidIntegerSubstring(input, 0, pos) then pos
  else firstI(input, pos + 1)
}

function firstJ(input: string, pos: int, i: int): int
  requires containsThreeSpaceSeparatedIntegers(input)
  requires  i + 1 <= pos <= |input| - 1
  decreases |input| - pos
{
  if input[pos] == ' ' && isValidIntegerSubstring(input, i + 1, pos) then pos
  else firstJ(input, pos + 1, i)
}

function firstK(input: string, pos: int, j: int): int
  requires containsThreeSpaceSeparatedIntegers(input)
  requires j + 1 <= pos <= |input|
  decreases |input| - pos
{
  if isValidIntegerSubstring(input, j + 1, pos) && (pos == |input| || input[pos] == '\n') then pos
  else firstK(input, pos + 1, j)
}

function parseThreeNumbers(input: string): (int, int, int)
  requires containsThreeSpaceSeparatedIntegers(input)
{
  var i := firstI(input, 1);
  var j := firstJ(input, i + 1, i);
  var k := firstK(input, j + 1, j);
  (substringToInt(input, 0, i), substringToInt(input, i + 1, j), substringToInt(input, j + 1, k))
}

// Lemmas proving that natToString and intToStringPure produce valid strings
lemma NatToStringProps(n: int)
  requires n >= 0
  ensures if n == 0 then natToString(n) == "0" else isDigitSequence(natToString(n)) && natToString(n)[0] != '0'
  decreases n
{
  if n == 0 {
    // natToString(0) == "0" by definition
  } else if n < 10 {
    // natToString(n) == digitToString(n) which is a single digit not '0' when n>0
  } else {
    // n >= 10
    NatToStringProps(n / 10);
    // From induction, natToString(n/10) is a digit sequence and its first char != '0'
    // natToString(n) = natToString(n/10) + digitToString(n%10)
    // We need to show the concatenation is a digit sequence and first char != '0'
    // Prove digit sequence for concatenation:
    var a := natToString(n / 10);
    var b := digitToString(n % 10);
    // Show isDigitSequence(a + b)
    // For all indices less than |a|, they are digits by induction.
    // For indices >= |a|, they index into b which is a single digit.
  }
}

lemma IntToStringIsValid(x: int)
  ensures isValidIntegerString(intToStringPure(x))
{
  if x == 0 {
    // "0" is valid by definition
  } else if x < 0 {
    var m := -x;
    NatToStringProps(m);
    // natToString(m) is a digit sequence and natToString(m)[0] != '0' (since m>0)
    // Therefore "-" + natToString(m) satisfies the isValidIntegerString predicate
  } else {
    // x > 0
    NatToStringProps(x);
    // natToString(x) is a digit sequence and first char != '0'
    // Therefore natToString(x) satisfies isValidIntegerString predicate
  }
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

