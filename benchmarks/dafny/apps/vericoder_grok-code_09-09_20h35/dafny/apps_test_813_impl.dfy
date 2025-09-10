predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && |SplitSpaces(lines[0])| >= 3 &&
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    n > 0
}

predicate ValidOutput(input: string, result: seq<char>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    |result| == 2 * n - 1 &&
    (forall i :: 0 <= i < n ==> result[2*i] == '1' || result[2*i] == '2') &&
    (forall i :: 0 <= i < n-1 ==> result[2*i+1] == ' ')
}

predicate CorrectAssignment(input: string, result: seq<char>)
    requires ValidInput(input)
    requires ValidOutput(input, result)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    forall i :: 1 <= i <= n ==> 
        (i in arthurSet ==> result[2*(i-1)] == '1') &&
        (i !in arthurSet ==> result[2*(i-1)] == '2')
}

// <vc-helpers>
function SplitLines(s: seq<char>): seq<seq<char>>
  decreases |s|
{
  if s == [] then []
  else if s[0] == '\n' then [ [] ] + SplitLines(s[1..])
  else var rest := SplitLines(s[1..]); 
       if rest == [] then [ [] + [s[0]] ] 
       else [ (rest[0] + [s[0]]) ] + rest[1..]
}

function SplitSpaces(s: seq<char>): seq<seq<char>>
  decreases |s|
{
  if s == [] then []
  else if s[0] == ' ' then 
    if |s| > 1 then SplitSpaces(s[1..]) else []
  else 
    var rest := SplitSpaces(s[1..]);
    if rest == [] then [ [s[0]] ] 
    else if rest[0] == [] then [ [s[0]] ] + rest[1..]
    else [ ([s[0]] + rest[0]) ] + rest[1..]
}

function ParseInt(digits: seq<char>): int
  requires |digits| > 0 && forall c :: c in digits ==> '0' <= c <= '9'
  decreases |digits|
{
  if digits == [] then 0
  else 10 * ParseInt(digits[..|digits|-1]) + (digits[|digits|-1] - '0')
}

function ParseIntSeq(ss: seq<seq<char>>): seq<int>
  decreases |ss|
{
  if ss == [] then []
  else [ParseInt(ss[0])] + ParseIntSeq(ss[1..])
}

predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && |SplitSpaces(lines[0])| >= 3 &&
    var nStr := SplitSpaces(lines[0])[0];
    |nStr| > 0 && forall c :: c in nStr ==> '0' <= c <= '9' &&
    var n := ParseInt(nStr);
    n > 0
}

predicate ValidOutput(input: string, result: seq<char>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    |result| == 2 * n - 1 &&
    (forall i :: 0 <= i < n ==> result[2*i] == '1' || result[2*i] == '2') &&
    (forall i :: 0 <= i < n-1 ==> result[2*i+1] == ' ')
}

predicate CorrectAssignment(input: string, result: seq<char>)
    requires ValidInput(input)
    requires ValidOutput(input, result)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    forall i :: 1 <= i <= n ==> 
        (i in arthurSet ==> result[2*(i-1)] == '1') &&
        (i notinSet ==> result[2*(i-1)] == '2')
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<char>)
    requires |input| > 0
    ensures !ValidInput(input) ==> |result| == 0
    ensures ValidInput(input) ==> ValidOutput(input, result) && CorrectAssignment(input, result)
    ensures forall i :: 0 <= i < |result| ==> result[i] == '1' || result[i] == '2' || result[i] == ' '
// </vc-spec>
// <vc-code>
{
  if !ValidInput(input) {
    result := [];
  } else {
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    result := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |result| == if i == 0 then 0 else 2 * i - 1
      invariant forall k :: 0 <= k < i ==> 
        if k+1 in arthurSet then result[2*k] == '1' else result[2*k] == '2'
      invariant forall k :: 0 <= k < i-1 ==> result[2*k+1] == ' '
    {
      if i > 0 {
        result := result + [' '];
      }
      if i+1 in arthurSet {
        result := result + ['1'];
      } else {
        result := result + ['2'];
      }
      i := i + 1;
    }
  }
  return result;
}
// </vc-code>

