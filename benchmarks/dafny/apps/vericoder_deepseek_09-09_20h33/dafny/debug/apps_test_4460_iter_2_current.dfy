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
function parseIntsHelper(s: string, pos: int, current: string, acc: seq<int>): seq<int>
  requires 0 <= pos <= |s|
  requires validInput(s)
  requires |current| == 0 || (forall i :: 0 <= i < |current| ==> ('0' <= current[i] <= '9') || (i == 0 && current[i] == '-'))
  decreases |s| - pos
{
  if pos == |s| then
    if |current| > 0 then acc + [stringToInt(current)]
    else acc
  else if s[pos] == ' ' || s[pos] == '\n' then
    if |current| > 0 then
      parseIntsHelper(s, pos + 1, "", acc + [stringToInt(current)])
    else
      parseIntsHelper(s, pos + 1, "", acc)
  else
    parseIntsHelper(s, pos + 1, current + [s[pos]], acc)
}

function stringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-')
{
  if s[0] == '-' then
    -stringToNat(s[1..])
  else
    stringToNat(s)
}

function stringToNat(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 0 then 0
  else (s[0] as int - '0' as int) * pow10(|s| - 1) + stringToNat(s[1..])
}

function pow10(n: nat): int
  decreases n
{
  if n == 0 then 1
  else 10 * pow10(n - 1)
}

function generateOutputHelper(numbers: seq<int>, index: int, result: string): string
  decreases |numbers| - index
{
  if index == |numbers| then
    result
  else
    generateOutputHelper(numbers, index + 1, 
      if |result| > 0 then result + " " + intToString(numbers[index])
      else intToString(numbers[index]))
}

function intToString(n: int): string
{
  if n < 0 then
    "-" + natToString(-n)
  else
    natToString(n)
}

function natToString(n: nat): string
  decreases n
{
  if n < 10 then
    [('0' as int + n) as char]
  else
    natToString(n / 10) + [('0' as int + n % 10) as char]
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
  var zeroIndex := findZeroIndex(numbers);
  var sum := 0;
  var i := 0;
  
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant sum == varSum(numbers, zeroIndex, i)
  {
    if i != zeroIndex {
      sum := sum + numbers[i];
    }
    i := i + 1;
  }
  
  var resultSeq := numbers[..zeroIndex] + [sum] + numbers[zeroIndex + 1..];
  result := generateOutput(resultSeq);
}

function varSum(numbers: seq<int>, skipIndex: int, count: int): int
  requires 0 <= skipIndex < |numbers|
  requires 0 <= count <= |numbers|
  decreases count
{
  if count == 0 then 0
  else varSum(numbers, skipIndex, count - 1) + (if count - 1 != skipIndex then numbers[count - 1] else 0)
}
// </vc-code>

