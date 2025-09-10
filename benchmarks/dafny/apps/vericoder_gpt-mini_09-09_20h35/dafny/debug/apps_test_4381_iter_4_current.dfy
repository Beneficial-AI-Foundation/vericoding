predicate ValidInput(trainFare: int, busFare: int)
{
    1 <= trainFare <= 100 && 1 <= busFare <= 100 && busFare % 2 == 0
}

function TotalCost(trainFare: int, busFare: int): int
    requires ValidInput(trainFare, busFare)
{
    trainFare + busFare / 2
}

// <vc-helpers>
function digitValue(c: char): int
  requires '0' <= c <= '9'
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else 9
}

function digitChar(i: int): string
  requires 0 <= i <= 9
{
  if i == 0 then "0"
  else if i == 1 then "1"
  else if i == 2 then "2"
  else if i == 3 then "3"
  else if i == 4 then "4"
  else if i == 5 then "5"
  else if i == 6 then "6"
  else if i == 7 then "7"
  else if i == 8 then "8"
  else "9"
}

function pow10(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

function isValidInteger(s: string): bool
{
  |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function stringToInt(s: string): int
  requires isValidInteger(s)
  decreases |s|
{
  if |s| == 0 then 0
  else if |s| == 1 then digitValue(s[0])
  else digitValue(s[0]) * pow10(|s| - 1) + stringToInt(s[1..])
}

function intToString(i: int): string
  requires i >= 0
  decreases i
{
  if i < 10 then "" + digitChar(i)
  else intToString(i / 10) + ("" + digitChar(i % 10))
}

function replace(s: string, oldStr: string, newStr: string): string
  requires oldStr == "\n" && newStr == ""
  decreases |s|
{
  if |s| == 0 then ""
  else if s[0] == oldStr[0] then replace(s[1..], oldStr, newStr)
  else s[0..1] + replace(s[1..], oldStr, newStr)
}

function indexOf(s: string, c: char, start: int): int
  requires 0 <= start <= |s|
  decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == c then start
  else indexOf(s, c, start + 1)
}

function split(s: string, sep: char): seq<string>
  decreases |s|
{
  if |s| == 0 then [""]
  else
    var idx := indexOf(s, sep, 0);
    if idx == -1 then [s]
    else
      var head := s[..idx];
      var tail := s[idx + 1..];
      [head] + split(tail, sep)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires exists i :: 0 <= i < |input| && input[i] == ' '
    requires var parts := split(replace(input, "\n", ""), ' '); 
             |parts| >= 2 && 
             isValidInteger(parts[0]) && 
             isValidInteger(parts[1])
    requires var parts := split(replace(input, "\n", ""), ' ');
             var trainFare := stringToInt(parts[0]);
             var busFare := stringToInt(parts[1]);
             ValidInput(trainFare, busFare)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var parts := split(replace(input, "\n", ""), ' ');
            var trainFare := stringToInt(parts[0]);
            var busFare := stringToInt(parts[1]);
            result == intToString(TotalCost(trainFare, busFare)) + "\n"
// </vc-spec>
// <vc-code>
{
  var s := replace(input, "\n", "");
  var parts := split(s, ' ');
  var trainFare := stringToInt(parts[0]);
  var busFare := stringToInt(parts[1]);
  var total := TotalCost(trainFare, busFare);
  result := intToString(total) + "\n";
  return;
}
// </vc-code>

