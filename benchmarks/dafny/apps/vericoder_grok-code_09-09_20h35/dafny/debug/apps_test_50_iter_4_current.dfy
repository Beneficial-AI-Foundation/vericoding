predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input &&
    var lines := SplitLinesFunc(input);
    |lines| >= 3 &&
    ValidIntLine(lines[0], 3) &&
    ValidIntLine(lines[1]) &&
    ValidIntLine(lines[2]) &&
    var firstLine := SplitIntsFunc(lines[0]);
    var S := SplitIntsFunc(lines[1]);
    var B := SplitIntsFunc(lines[2]);
    |firstLine| == 3 && firstLine[0] >= 1 && firstLine[1] >= 1 && firstLine[2] >= 1 &&
    |S| == firstLine[0] && |B| == firstLine[1]
}

function ParseInput(input: string): (int, int, int, seq<int>, seq<int>)
    requires ValidInput(input)
    ensures var result := ParseInput(input);
        result.0 >= 1 && result.1 >= 1 && result.2 >= 1 &&
        |result.3| == result.0 && |result.4| == result.1 &&
        (forall i :: 0 <= i < |result.3| ==> result.3[i] >= 1) &&
        (forall i :: 0 <= i < |result.4| ==> result.4[i] >= 1)
{
    var lines := SplitLinesFunc(input);
    var firstLine := SplitIntsFunc(lines[0]);
    var S := SplitIntsFunc(lines[1]);
    var B := SplitIntsFunc(lines[2]);
    (firstLine[0], firstLine[1], firstLine[2], S, B)
}

function ComputeMaxBourles(r: int, S: seq<int>, B: seq<int>): int
    requires r >= 1
    requires |S| >= 1 && |B| >= 1
    requires forall i :: 0 <= i < |S| ==> S[i] >= 1
    requires forall i :: 0 <= i < |B| ==> B[i] >= 1
{
    var x := MinSeqFunc(S);
    var y := MaxSeqFunc(B);
    var cnt := (r % x) + (r / x) * y;
    if r > cnt then r else cnt
}

// <vc-helpers>
function IsDigit(c: char): bool
{
  '0' <= c <= '9'
}

function IsSpace(c: char): bool
{
  c == ' ' || c == '\t'
}

function CharToDigit(c: char): int
  requires IsDigit(c)
{
  (c as int) - ('0' as int)
}

function Power10(e: nat): nat
{
  if e == 0 then 1 else 10 * Power10(e-1)
}

function IndexOfnewline(s: string, start: nat): int
  requires start <= |s|
{
  if start == |s| then -1
  else if s[start] == '\n' then start
  else IndexOfnewline(s, start+1)
}

function SplitLinesFunc(input: string): seq<string>
  decreases |input|
{
  if input == "" then []
  else
  var i := IndexOfnewline(input, 0);
  if i == -1 then [input]
  else
  var line := input[0..i];
  var rest := input[i+1..];
  [line] + SplitLinesFunc(rest)
}

function SkipSpaces(s: string, start: nat): nat
  requires start <= |s|
  decreases |s| - start
{
  if start == |s| then start
  else if IsSpace(s[start]) then SkipSpaces(s, start+1)
  else start
}

function EndOfToken(s: string, start: nat): nat
  requires start <= |s|
  decreases |s| - start
{
  if start == |s| then start
  else if not IsSpace(s[start]) then EndOfToken(s, start+1)
  else start
}

function ParseInt(s: string): int
  requires ValidIntToken(s)
{
  if s[0] == '-' then -ParseNat(s[1..]) as int
  else ParseNat(s) as int
}

function ParseNat(s: string): nat
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> IsDigit(s[i])
{
  if |s| == 1 then CharToDigit(s[0])
  else CharToDigit(s[0]) * Power10(|s|-1) + ParseNat(s[1..])
}

function SplitIntsFunc(line: string): seq<int>
  decreases |line|
{
  var start := SkipSpaces(line, 0);
  if start == |line| then []
  else
  var end := EndOfToken(line, start);
  var token := line[start..end];
  [ParseInt(token)] + SplitIntsFunc(line[end..])
}

predicate ValidIntToken(token: string)
{
  |token| > 0 &&
  (token[0] == '-' || IsDigit(token[0])) &&
  forall i :: (token[0] == '-' ? 1 : 0) <= i < |token| ==> IsDigit(token[i])
}

function ValidIntLine(line: string): bool
{
  CheckTokens(line, 0)
}

function ValidIntLine(line: string, count: int): bool
{
  ValidIntLine(line) && |SplitIntsFunc(line)| == count
}

function CheckTokens(line: string, start: nat): bool
  requires start <= |line|
  decreases |line| - start
{
  var s := SkipSpaces(line, start);
  if s == |line| then true
  else
  var e := EndOfToken(line, s);
  if e == s then false
  else if not ValidIntToken(line[s..e]) then false
  else CheckTokens(line, e)
}

function MinSeqFunc(nums: seq<int>): int
  requires |nums| > 0
  ensures forall i :: 0 <= i < |nums| ==> MinSeqFunc(nums) <= nums[i]
  ensures exists i :: 0 <= i < |nums| ==> MinSeqFunc(nums) == nums[i]
{
  if |nums| == 1 then nums[0]
  else if nums[0] < MinSeqFunc(nums[1..]) then nums[0]
  else MinSeqFunc(nums[1..])
}

function MaxSeqFunc(nums: seq<int>): int
  requires |nums| > 0
  ensures forall i :: 0 <= i < |nums| ==> MaxSeqFunc(nums) >= nums[i]
  ensures exists i :: 0 <= i < |nums| ==> MaxSeqFunc(nums) == nums[i]
{
  if |nums| == 1 then nums[0]
  else if nums[0] > MaxSeqFunc(nums[1..]) then nums[0]
  else MaxSeqFunc(nums[1..])
}

function DigitToChar(n: nat): char
  requires 0 <= n <= 9
{
  char.FromInt(('0' as int) + n)
}

function IntToDigits(n: nat): string
  decreases n
{
  if n == 0 then []
  else [DigitToChar(n % 10)] + IntToDigits(n / 10)
}

function Reverse(s: seq<char>): seq<char>
  decreases |s|
{
  if |s| == 0 then []
  else Reverse(s[1..]) + [s[0]]
}

function IntToStringNat(n: nat): string
{
  if n == 0 then "0"
  else Reverse(IntToDigits(n))
}

function IntToStringFunc(n: int): string
{
  if n < 0 then "-" + IntToStringNat(-(n))  // assuming n >= -2^63 for int64, but in math unlimited
  else IntToStringNat(n)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires '\n' in input
    requires ValidInput(input)
    ensures |result| > 0
    ensures exists n, m, r, S, B :: 
        ParseInput(input) == (n, m, r, S, B) &&
        n >= 1 && m >= 1 && r >= 1 &&
        |S| == n && |B| == m &&
        (forall i :: 0 <= i < |S| ==> S[i] >= 1) &&
        (forall i :: 0 <= i < |B| ==> B[i] >= 1) &&
        result == IntToStringFunc(ComputeMaxBourles(r, S, B)) + "\n"
// </vc-spec>
// <vc-code>
{
  var (n, m, r, S, B) := ParseInput(input);
  var maxB := ComputeMaxBourles(r, S, B);
  var res := IntToStringFunc(maxB) + "\n";
  return res;
}
// </vc-code>

