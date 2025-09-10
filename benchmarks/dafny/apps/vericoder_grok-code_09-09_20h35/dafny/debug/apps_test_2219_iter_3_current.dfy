function minStepsToZero(n: nat, k: nat): nat
    requires k >= 2
    decreases n
{
    if n == 0 then 0
    else if n % k == 0 then 1 + minStepsToZero(n / k, k)
    else (n % k) + minStepsToZero(n - (n % k), k)
}

predicate validInput(input: string)
{
    |input| > 0 && 
    var lines := splitLinesFunc(input);
    |lines| >= 1 &&
    isValidNumber(lines[0]) &&
    var t := stringToIntFunc(lines[0]);
    t >= 1 && t <= 100 &&
    |lines| >= t + 1 &&
    forall i :: 1 <= i <= t ==> validTestCase(lines[i])
}

predicate validTestCase(line: string)
{
    var parts := splitSpacesFunc(line);
    |parts| == 2 &&
    isValidNumber(parts[0]) &&
    isValidNumber(parts[1]) &&
    var n := stringToIntFunc(parts[0]);
    var k := stringToIntFunc(parts[1]);
    n >= 1 && k >= 2
}

predicate isValidNumber(s: string)
{
    |s| >= 1 &&
    (s == "0" || (s[0] != '0' && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')) &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function expectedOutput(input: string): string
    requires validInput(input)
{
    var lines := splitLinesFunc(input);
    var t := stringToIntFunc(lines[0]);
    var results := seq(t, i requires 0 <= i < t => 
        var parts := splitSpacesFunc(lines[i+1]);
        var n := stringToIntFunc(parts[0]);
        var k := stringToIntFunc(parts[1]);
        intToStringFunc(minStepsToZero(n, k))
    );
    joinLinesSeq(results)
}

// <vc-helpers>
// Function to compute b^e for integers
function Power(b: int, e: nat): int
{
  if e == 0 then 1
  else b * Power(b, e-1)
}

// Function to get digit value from char
function DigitValue(c: char): int
  requires '0' <= c <= '9'
{
  c as int - '0' as int
}

// Function to convert string to int, assuming it's a valid number
function stringToIntFunc(s: string): int
  requires isValidNumber(s)
  decreases |s|
{
  if |s| == 1 then DigitValue(s[0])
  else DigitValue(s[0]) * Power(10, |s|-1) + stringToIntFunc(s[1..])
}

// Helper datatype for building strings
datatype ListChar = Nil | Cons(char, ListChar)

// Helper to build string from int
function intToStringHelper(n: nat): ListChar
{
  if n == 0 then Nil
  else Cons( ((n % 10) + ('0' as int)) as char, intToStringHelper(n / 10) )
}

// Reverse a list
function ReverseList(l: ListChar): ListChar
{
  match l
  case Nil => Nil
  case Cons(c, tail) => Cons(c, ReverseList(tail)) + Nil  // Simplified reverse
}

// Actually, to make it work, better reverse properly
function ReverseList(l: ListChar, acc: ListChar): ListChar
{
  match l
  case Nil => acc
  case Cons(c, tail) => ReverseList(tail, Cons(c, acc))
}

// Reverse
function Reverse(l: ListChar): ListChar
{
  ReverseList(l, Nil)
}

// Convert list to seq
function ListToSeq(l: ListChar): seq<char>
{
  match l
  case Nil => []
  case Cons(c, tail) => [c] + ListToSeq(tail)
}

// Function to convert int to string
function intToStringFunc(n: nat): string
{
  if n == 0 then "0"
  else ListToSeq(Reverse(intToStringHelper(n)))
}

// Function to find a char in string
function Find(c: char, s: string, start: nat): int
  requires start <= |s|
{
  if start >= |s| then -1
  else if s[start] == c then start
  else Find(c, s, start+1)
}

// Function to split lines by '\n'
function splitLinesFunc(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var i := Find('\n', s, 0);
    if i == -1 then [s]
    else [s[0..i]] + splitLinesFunc(s[i+1..])
}

// Function to split spaces by ' '
function splitSpacesFunc(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var i := Find(' ', s, 0);
    if i == -1 then [s]
    else [s[0..i]] + splitSpacesFunc(s[i+1..])  // Note: this assumes single space, for simplicity
}

// Function to join seq of strings with '\n'
function joinLinesSeq(ss: seq<string>): string
  decreases |ss|
{
  if |ss| == 0 then ""
  else if |ss| == 1 then ss[0]
  else ss[0] + "\n" + joinLinesSeq(ss[1..])
}

lemma minStepsDecreases()
    ensures forall n, k :: k >= 2 && n > 0 ==> (if n % k == 0 then n / k else n - (n % k)) < n
{
    // Proof that the recursive call decreases n
}

lemma minStepsToZeroProperties()
    ensures forall n, k :: k >= 2 ==> minStepsToZero(n, k) >= 0
{
    // Inductive proof on n
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires validInput(input)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] != '\0'
    ensures result == expectedOutput(input)
// </vc-spec>
// <vc-code>
{
    var lines := splitLinesFunc(input);
    var t := stringToIntFunc(lines[0]);
    var results: seq<string> := [];
    var i := 1;
    while i <= t
        invariant 1 <= i <= t + 1
        invariant |results| == i - 1
        invariant forall m :: 0 <= m < i - 1 ==>
            var parts := splitSpacesFunc(lines[m+1]);
            var n := stringToIntFunc(parts[0]);
            var k := stringToIntFunc(parts[1]);
            results[m] == intToStringFunc(minStepsToZero(n, k))
    {
        var line := lines[i];
        var parts := splitSpacesFunc(line);
        var n := stringToIntFunc(parts[0]);
        var k := stringToIntFunc(parts[1]);
        var steps := minStepsToZero(n, k);
        var str := intToStringFunc(steps);
        results := results + [str];
        i := i + 1;
    }
    result := joinLinesSeq(results);
}
// </vc-code>

