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
function stringToIntFunc(s: string): int
  requires isValidNumber(s)
  reads {}
{
  if s == "0" then 0
  else
    var n := 0;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant n == (if i == 0 then 0 else stringToNatAccumulate(s[..i]))
      invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
    {
      n := n * 10 + (s[i] as int - '0' as int);
      i := i + 1;
    }
    n
}

function stringToNatAccumulate(s: string): nat
  requires isValidNumber(s) || s == ""
  reads {}
{
  if s == "" then 0
  else
    var n := 0;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant n == (if i == 0 then 0 else stringToNatAccumulate(s[..i]))
      invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
    {
      n := n * 10 + (s[i] as int - '0' as int);
      i := i + 1;
    }
    n as nat
}


function intToStringFunc(n: nat): string
  ensures isValidNumber(intToStringFunc(n))
  ensures n == stringToIntFunc(intToStringFunc(n))
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (s == "" && temp == n) || (s != "" && s[0] != '0' && forall c :: c in s ==> '0' <= c <= '9')
      invariant (s == "" && temp == n) || n == (stringToIntFunc(intToStringInternal(n / (10 * (temp / 10)), temp, s)))
    {
      s := (temp % 10 as char + '0' as char) + s;
      temp := temp / 10;
    }
    s
}

function intToStringInternal(original_n: nat, temp: nat, s: string): string
  requires temp >= 0
  requires s == "" || (s[0] != '0' && forall c :: c in s ==> '0' <= c <= '9')
  reads {}
  decreases temp
{
  if temp == 0 then s
  else intToStringInternal(original_n, temp / 10, ((temp % 10 as char + '0' as char) + s))
}

function splitLinesFunc(s: string): seq<string>
  reads {}
{
  if s == "" then []
  else
    var result: seq<string> := [];
    var currentLine: string := "";
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < |result| ==> !('\n' in result[j])
      invariant !('\n' in currentLine)
    {
      if s[i] == '\n'
      {
        result := result + [currentLine];
        currentLine := "";
      }
      else
      {
        currentLine := currentLine + s[i];
      }
      i := i + 1;
    }
    result + [currentLine]
}

function splitSpacesFunc(s: string): seq<string>
  reads {}
{
  if s == "" then []
  else
    var result: seq<string> := [];
    var current: string := "";
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < |result| ==> !(' ' in result[j])
      invariant !(' ' in current)
    {
      if s[i] == ' '
      {
        if current != ""
        {
          result := result + [current];
        }
        current := "";
      }
      else
      {
        current := current + s[i];
      }
      i := i + 1;
    }
    if current != "" then result + [current] else result
}

function joinLinesSeq(lines: seq<string>): string
  reads {}
  ensures (forall i :: 0 <= i < |joinLinesSeq(lines)| ==> joinLinesSeq(lines)[i] != '\0')
{
  if |lines| == 0 then ""
  else if |lines| == 1 then lines[0]
  else lines[0] + "\n" + joinLinesSeq(lines[1..])
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
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant |results] == i
    invariant t == stringToIntFunc(lines[0])
    invariant forall j :: 0 <= j < i ==> isValidNumber(results[j])
    invariant validInput(input)
    invariant lines == splitLinesFunc(input)
    invariant |lines| >= t + 1
    invariant forall k :: 1 <= k <= t ==> validTestCase(lines[k])
  {
    var parts := splitSpacesFunc(lines[i+1]);
    var n_str := parts[0];
    var k_str := parts[1];
    assert isValidNumber(n_str);
    assert isValidNumber(k_str);
    var n := stringToIntFunc(n_str);
    var k := stringToIntFunc(k_str);
    var steps := minStepsToZero(n, k);
    results := results + [intToStringFunc(steps)];
    i := i + 1;
  }
  result := joinLinesSeq(results);
}
// </vc-code>

