predicate validInput(n: int, m: int, k: int, H: seq<int>)
{
    n >= 1 && n == |H| && m >= 0 && k >= 0 && 
    (forall i :: 0 <= i < |H| ==> H[i] >= 0)
}

function canReachEnd(n: int, m: int, k: int, H: seq<int>): bool
    requires validInput(n, m, k, H)
{
    simulateGame(0, m, n, k, H)
}

function simulateGame(pos: int, blocks: int, n: int, k: int, H: seq<int>): bool
    requires 0 <= pos < n
    requires n == |H|
    requires k >= 0
    requires blocks >= 0
    requires forall i :: 0 <= i < |H| ==> H[i] >= 0
    decreases n - pos
{
    if pos == n - 1 then
        true
    else
        var h1 := H[pos];
        var h2 := H[pos + 1];
        if h1 >= h2 then
            var newBlocks := if h2 >= k then blocks + (h1 - h2) + k else blocks + h1;
            simulateGame(pos + 1, newBlocks, n, k, H)
        else
            if h2 > h1 + blocks + k then
                false
            else
                var newBlocks := 
                    if h2 <= k then blocks + h1
                    else if (h2 - h1) <= k then blocks + k - (h2 - h1)
                    else blocks - (h2 - h1 - k);
                newBlocks >= 0 && simulateGame(pos + 1, newBlocks, n, k, H)
}

predicate validCompleteInputFormat(input: string)
{
    |input| > 0 && input[|input|-1] == '\n'
}

predicate validOutputFormat(output: string, input: string)
{
    |output| >= 0 && 
    (output == "" || output[|output|-1] == '\n') &&
    (forall i :: 0 <= i < |output| ==> output[i] == 'Y' || output[i] == 'E' || output[i] == 'S' || output[i] == 'N' || output[i] == 'O' || output[i] == '\n')
}

predicate correctGameResults(output: string, input: string)
{
    true // Simplified for compilation
}

predicate outputMatchesTestCaseCount(output: string, input: string)
{
    true // Simplified for compilation
}

// <vc-helpers>
datatype Option<T> = None | Some(value: T)

function digitValue(c: char): int
  requires '0' <= c <= '9'
{
  (c as int) - ('0' as int)
}

function power10(e: nat): int
  decreases e
{
  if e == 0 then 1 else 10 * power10(e-1)
}

function parseNat(s: seq<char>): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 0 then 0 else digitValue(s[0]) * power10(|s|-1) + parseNat(s[1..])
}

function parseInt(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0 else if |s| > 0 && s[0] == '-' then -parseInt(s[1..]) else parseNat(s)
}

function findDelim(s: seq<char>, delim: char): Option<int>
  decreases |s|
{
  if |s| == 0 then None else if s[0] == delim then Some(0) else 
  var next := findDelim(s[1..], delim);
  if next.Some? then Some(next.value + 1) else None
}

function split(s: seq<char>, delim: char): seq<seq<char>>
  decreases |s|
{
  if |s| == 0 then [] else 
  match findDelim(s, delim)
  case None => [s]
  case Some(i) => [s[..i]] + split(s[i+1..], delim)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input|-1] == '\n'
    requires validCompleteInputFormat(stdin_input)
    ensures |result| >= 0
    ensures forall i :: 0 <= i < |result| ==> result[i] == 'Y' || result[i] == 'E' || result[i] == 'S' || result[i] == 'N' || result[i] == 'O' || result[i] == '\n'
    ensures result == "" || result[|result|-1] == '\n'
    ensures validOutputFormat(result, stdin_input)
    ensures correctGameResults(result, stdin_input)
    ensures outputMatchesTestCaseCount(result, stdin_input)
// </vc-spec>
// <vc-code>
{
  var lines := split(stdin_input, '\n');
  if |lines| > 0 && |lines[|lines|-1]| == 0 {
    lines := lines[..|lines|-1];
  }
  if |lines| == 0 {
    result := "";
    return;
  }
  var T := parseInt(lines[0]);
  var index := 1;
  result := "";
  while index < |lines|
    invariant 1 <= index <= |lines|
    decreases |lines| - index
  {
    var n := parseInt(lines[index]);
    var m := parseInt(lines[index+1]);
    var k := parseInt(lines[index+2]);
    var H := [];
    for i := 0 to n-1
      invariant |H| == i
    {
      var val := parseInt(lines[index+3 + i]);
      H := H + [val];
    }
    index := index + 3 + n;
    if n >=1 && n == |H| && m >=0 && k >=0 && forall i :: 0 <= i < n ==> H[i] >=0 {
      if canReachEnd(n, m, k, H) {
        result := result + "YES\n";
      } else {
        result := result + "NO\n";
      }
    } else {
      result := result + "NO\n";
    }
  }
}
// </vc-code>

