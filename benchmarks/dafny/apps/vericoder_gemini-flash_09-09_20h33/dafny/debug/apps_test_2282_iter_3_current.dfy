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
function intToString(n: int): string
  ensures (n == 0) ==> (intToString(n) == "0")
  ensures (n > 0) ==> (var s := intToString(n); (s[0] >= '1' && s[0] <= '9'))
  ensures (n < 0) ==> (var s := intToString(n); s[0] == '-')
  decreases n
{
  if n == 0 then
    "0"
  else if n > 0 then
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (var current_temp := temp; var current_s := s;
                 var acc := 0; var pow := 1;
                 while current_temp > 0
                 decreases current_temp
                 {
                   acc := acc + (current_temp % 10) * pow;
                   pow := pow * 10;
                   current_temp := current_temp / 10;
                 }
                 n == acc + (if current_s == "" then 0 else parseInteger(current_s)) * pow)
    {
      s := (('0' as int + (temp % 10)) as char) + s;
      temp := temp / 10;
    }
    s
  else // n < 0
    "-" + intToString(-n)
}

function parseInteger(s: string): int
  requires isValidInteger(s)
  decreases |s|
{
  if s == "" then 0
  else if s[0] == '-' then -parseInteger(s[1..])
  else
    var n := 0;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
      invariant n == (if i == 0 then 0 else var res := 0; for k := 0 to i-1 { res := res * 10 + (s[k] as int - '0' as int); } res)
    {
      n := n * 10 + (s[i] as int - '0' as int);
      i := i + 1;
    }
    n
}


predicate isValidInteger(s: string)
{
    |s| > 0 &&
    (s[0] == '-' ==> (|s| > 1 && (forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'))) &&
    (s[0] != '-' ==> (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'))
}

function split(s: string, separator: char): seq<string>
  requires separator as int != '\n' as int || s == "" || exists i :: 0 <= i < |s| && s[i] == '\n'
  ensures forall i :: 0 <= i < |split(s, separator)| ==> !split(s, separator)[i].Contains(separator)
{
  if s == "" then
    []
  else
    var result: seq<string> := [];
    var currentPart := "";
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant separator as int != '\n' as int || s == "" || exists k :: 0 <= k < |s| && s[k] == '\n'
      invariant forall k :: 0 <= k < |result| ==> !result[k].Contains(separator)
      invariant !currentPart.Contains(separator)
    {
      if s[i] == separator then
        result := result + [currentPart];
        currentPart := "";
      else
        currentPart := currentPart + s[i];
      i := i + 1;
    }
    result + [currentPart]
}

function method Contains(s: string, char: char): bool
{
  exists i :: 0 <= i < |s| && s[i] == char
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
  if ValidCommandInput(input)
  {
    var lines := split(input, '\n');
    var n := parseInteger(lines[0]);
    result := intToString(n + 1) + "\n";
  }
  else
  {
    result := "";
  }
}
// </vc-code>

