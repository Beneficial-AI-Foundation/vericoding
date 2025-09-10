predicate validInput(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> s[i] == ' ' || s[i] == '\n' || ('0' <= s[i] <= '9') || s[i] == '-')
}

predicate validNumber(s: string)
{
    |s| == 0 || (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-'))
}

function countZeros(numbers: seq<int>): int
{
    if |numbers| == 0 then 0
    else (if numbers[0] == 0 then 1 else 0) + countZeros(numbers[1..])
}

function findZeroIndex(numbers: seq<int>): int
    requires |numbers| > 0
    requires countZeros(numbers) == 1
{
    if numbers[0] == 0 then 0
    else if |numbers| > 1 then 1 + findZeroIndex(numbers[1..])
    else 0
}

function parseInts(s: string): seq<int>
    requires |s| > 0
    requires validInput(s)
{
    parseIntsHelper(s, 0, "", [])
}

function generateOutput(numbers: seq<int>): string
{
    generateOutputHelper(numbers, 0, "")
}

// <vc-helpers>
function StringToInt(s: string): int
reads s
  requires |s| > 0
  requires validNumber(s)
{
  var i := 0;
  var sign := 1;
  var num := 0;
  if s[0] == '-'
  {
    sign := -1;
    i := 1;
  }
  while i < |s|
  invariant 0 <= i <= |s|
  invariant num >= 0
  {
    num := num * 10 + (s[i] - '0');
    i := i + 1;
  }
  return sign * num;
}

function IntToString(n: int): string
  requires true // Can convert any integer
{
  if n == 0 then
    "0"
  else if n < 0 then
    "-" + IntToString(-n)
  else
  {
    var s := "";
    var temp_n := n;
    while temp_n > 0
    {
      s := (('0' + (temp_n % 10))) + s;
      temp_n := temp_n / 10;
    }
    s
  }
}

function parseIntsHelper(s: string, index: int, currentNumString: string, nums: seq<int>): seq<int>
    requires 0 <= index <= |s|
    // This invariant is tricky. It relates to the length of currentNumString remaining within the bounds of what's been processed from 's'.
    // A simpler approach for verification is to just ensure currentNumString is a valid number if non-empty.
    requires validNumber(currentNumString)
    reads s
    // This is a postcondition, not an invariant for the function itself as specified.
    // The previous ensures clause `forall i :: 0 <= i < |nums| ==> '0' <= s[i] <= '9' || s[i] == '-'` seems misplaced and incorrect.
    // The `nums` sequence is a result of parsing, not directly related to `s[i]`.
    // The correct property would be that numbers in `nums` are indeed integers.
    // However, the function returns a `seq<int>`, which inherently means they are integers.
{
    if index == |s| then
        if |currentNumString| > 0
            then nums + [StringToInt(currentNumString)]
        else
            nums
    else
        var c := s[index];
        if '0' <= c <= '9' || c == '-' then
            parseIntsHelper(s, index + 1, currentNumString + c, nums)
        else if c == ' ' || c == '\n' then
            if |currentNumString| > 0
                then parseIntsHelper(s, index + 1, "", nums + [StringToInt(currentNumString)])
            else
                parseIntsHelper(s, index + 1, "", nums)
        else
            // Should not happen given validInput, but to maintain safety, we pass on the currentNumString.
            // Or, more robustly, we could assert what we expect from `validInput`.
            parseIntsHelper(s, index + 1, currentNumString, nums)
}

function generateOutputHelper(numbers: seq<int>, index: int, currentOutput: string): string
    requires 0 <= index <= |numbers|
    // `reads numbers` means the function reads the object `numbers`. This is fine.
    reads numbers
    ensures |currentOutput| >= 0 // This is always true for any string. A stronger postcondition might be desired if specific output format is required.
{
    if index == |numbers| then
        currentOutput
    else
        var numString := IntToString(numbers[index]);
        // The first number should not have a leading space.
        var separator := if index == 0 && |currentOutput| == 0 then "" else " ";
        // Concatenate sequence of chars with `+`.
        generateOutputHelper(numbers, index + 1, currentOutput + separator + numString)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires validInput(input)
    requires |input| > 0
    ensures var numbers := parseInts(input);
            result == generateOutput(numbers)
// </vc-spec>
// <vc-code>
{
    var numbers := parseInts(input);
    result := generateOutput(numbers);
}
// </vc-code>

