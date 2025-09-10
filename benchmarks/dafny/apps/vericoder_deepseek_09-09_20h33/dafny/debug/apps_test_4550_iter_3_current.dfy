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
function ExtractNumbers(input: string, pos: int, acc: seq<int>, current: string): seq<int>
  requires |input| > 0
  requires 0 <= pos <= |input|
  requires forall x :: x in acc ==> x >= 0
  requires forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9'
  decreases |input| - pos
{
  if pos == |input| then
    if |current| > 0 then
      acc + [StringToInt(current)]
    else
      acc
  else if input[pos] == ' ' then
    if |current| > 0 then
      ExtractNumbers(input, pos + 1, acc + [StringToInt(current)], "")
    else
      ExtractNumbers(input, pos + 1, acc, "")
  else
    ExtractNumbers(input, pos + 1, acc, current + [input[pos]])
}

function StringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures 0 <= StringToInt(s)
{
  if |s| == 1 then
    s[0] as int - '0' as int
  else
    (s[0] as int - '0' as int) * pow10(|s| - 1) + StringToInt(s[1..])
}

function pow10(n: nat): int
  decreases n
  ensures pow10(n) >= 1
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

lemma ExtractNumbersValid(input: string)
  requires |input| > 0
  requires ValidInputFormat(input)
  ensures var nums := ExtractNumbers(input, 0, [], "");
          |nums| >= 3 && 
          (forall i :: 0 <= i < 3 ==> 1 <= nums[i] <= 100)
{
}

lemma ParseThreeIntsValid(input: string)
  requires |input| > 0
  requires ValidInputFormat(input)
  ensures ParseThreeIntsFunc(input).0 >= 1 && ParseThreeIntsFunc(input).1 >= 1 && ParseThreeIntsFunc(input).2 >= 1
  ensures ParseThreeIntsFunc(input).0 <= 100 && ParseThreeIntsFunc(input).1 <= 100 && ParseThreeIntsFunc(input).2 <= 100
{
}

lemma ExtractNumbersNonNegative(input: string, pos: int, acc: seq<int>, current: string)
  requires |input| > 0
  requires 0 <= pos <= |input|
  requires forall x :: x in acc ==> x >= 0
  requires forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9'
  ensures forall x :: x in ExtractNumbers(input, pos, acc, current) ==> x >= 0
  decreases |input| - pos
{
}

lemma ExtractNumbersCurrentValid(input: string, pos: int, acc: seq<int>, current: string)
  requires |input| > 0
  requires 0 <= pos <= |input|
  requires forall x :: x in acc ==> x >= 0
  requires forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9'
  ensures forall i :: 0 <= i < |current| + (|input| - pos) ==> '0' <= (current + input[pos..])[i] <= '9'
  decreases |input| - pos
{
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
  
  if a + b == c || b + c == a || c + a == b {
    result := "Yes\n";
  } else {
    result := "No\n";
  }
}
// </vc-code>

