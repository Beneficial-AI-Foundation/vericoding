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
  requires forall i :: 0 <= i < |acc| ==> acc[i] != 0
  decreases |s| - pos
  ensures forall i :: 0 <= i < |result| ==> result[i] != 0
{
  if pos == |s| then
    if |current| > 0 then 
      var num := stringToInt(current);
      assert num != 0;
      acc + [num]
    else acc
  else if s[pos] == ' ' || s[pos] == '\n' then
    if |current| > 0 then
      var num := stringToInt(current);
      assert num != 0;
      parseIntsHelper(s, pos + 1, "", acc + [num])
    else
      parseIntsHelper(s, pos + 1, "", acc)
  else
    parseIntsHelper(s, pos + 1, current + [s[pos]], acc)
}

function stringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || (i == 0 && s[i] == '-')
  ensures result != 0
{
  if s[0] == '-' then
    var sub := s[1..];
    assert |sub| > 0;
    -stringToNat(sub)
  else
    stringToNat(s)
}

function stringToNat(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
  ensures result >= 0
{
  if |s| == 1 then
    s[0] as int - '0' as int
  else 
    var rest := s[1..];
    var rest_val: int := stringToNat(rest);
    (s[0] as int - '0' as int) * pow10(|s| - 1) + rest_val
}

function pow10(n: nat): int
  decreases n
  ensures result >= 1
{
  if n == 0 then 1
  else 10 * pow10(n - 1)
}

function generateOutputHelper(numbers: seq<int>, index: int, result: string): string
  requires 0 <= index <= |numbers|
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

function varSum(numbers: seq<int>, skipIndex: int, count: int): int
  requires 0 <= skipIndex < |numbers|
  requires 0 <= count <= |numbers|
  decreases count
{
  if count == 0 then 0
  else varSum(numbers, skipIndex, count - 1) + (if count - 1 == skipIndex then 0 else numbers[count - 1])
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
  assert |numbers| > 0;
  assert countZeros(numbers) == 1;
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
  
  var resultSeq := numbers[0..zeroIndex] + [sum] + numbers[zeroIndex + 1..|numbers|];
  result := generateOutput(resultSeq);
}
// </vc-code>

