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
  if s[0] == '-' then
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
    // This pre-condition is not valid for `validNumber` because '-' can only be at the beginning
    // requires validNumber(currentNumString)
    reads s
{
    if index == |s| then
        if |currentNumString| > 0 && validNumber(currentNumString)
            then nums + [StringToInt(currentNumString)]
        else
            nums
    else
        var c := s[index];
        if '0' <= c <= '9' || c == '-' then
            parseIntsHelper(s, index + 1, currentNumString + c, nums)
        else if c == ' ' || c == '\n' then
            if |currentNumString| > 0 && validNumber(currentNumString)
                then parseIntsHelper(s, index + 1, "", nums + [StringToInt(currentNumString)])
            else
                parseIntsHelper(s, index + 1, "", nums)
        else
            parseIntsHelper(s, index + 1, currentNumString, nums)
}

function generateOutputHelper(numbers: seq<int>, index: int, currentOutput: string): string
    requires 0 <= index <= |numbers|
    reads numbers
    ensures |currentOutput| >= 0
{
    if index == |numbers| then
        currentOutput
    else
        var numString := IntToString(numbers[index]);
        var separator := if index == 0 && |currentOutput| == 0 then "" else " ";
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

