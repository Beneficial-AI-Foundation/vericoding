predicate ValidInput(input: string)
{
    |input| > 0 && exists i :: 0 <= i < |input| && input[i] == '\n'
}

predicate ValidCommandInput(input: string)
{
    var lines := split(input, '\n');
    |lines| >= 2 && lines[0] != "" && isValidInteger(lines[0])
}

function ExtractN(input: string): int
    requires ValidCommandInput(input)
{
    var lines := split(input, '\n');
    parseInteger(lines[0])
}

predicate CorrectOutput(input: string, result: string)
{
    ValidCommandInput(input) ==> 
        result == intToString(ExtractN(input) + 1) + "\n"
}

// <vc-helpers>
function findFirst(s: string, sep: char, i: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then |s|
  else if s[i] == sep then i
  else findFirst(s, sep, i + 1)
}

function split(s: string, sep: char): seq<string>
{
  var j := findFirst(s, sep, 0);
  if j == |s| then [s, ""] else [s[..j], s[j+1..]]
}

function isValidInteger(s: string): bool
{
  |s| > 0 && (forall i :: 0 <= i < |s| ==> ord(s[i]) >= ord('0') && ord(s[i]) <= ord('9'))
}

function parseAcc(s: string, i: int, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else parseAcc(s, i + 1, acc * 10 + (ord(s[i]) - ord('0')))
}

function parseInteger(s: string): int
{
  if isValidInteger(s) then parseAcc(s, 0, 0) else 0
}

function intToString(n: int): string
  requires n >= 0
  decreases n
{
  if n < 10 then [char(ord('0') + n)]
  else intToString(n / 10) + [char(ord('0') + (n % 10))]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
    ensures !ValidCommandInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
  if (!ValidCommandInput(input)) {
    result := "";
    return;
  }
  var n := ExtractN(input);
  result := intToString(n + 1) + "\n";
  return;
}
// </vc-code>

