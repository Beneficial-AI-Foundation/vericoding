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
function Pow10(power: int): int
  requires power >= 0
{
  if power == 0 then 1 else 10 * Pow10(power - 1)
}

function stringToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures stringToInt(s) >= 0
{
  if |s| == 0 then 0
  else (s[|s|-1] as int - '0' as int) + 10 * stringToInt(s[..|s|-1])
}

function intToString(n: int): string
  requires n >= 0
  ensures (n == 0) == (|intToString(n)| == 1 && intToString(n)[0] == '0')
  ensures n > 0 ==> |intToString(n)| > 0
  ensures n > 0 ==> intToString(n)[0] != '0'
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (temp == 0) == (s == "")
      invariant n > 0 ==> (temp > 0 || s != "")
      invariant n >= temp
      invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
      invariant (temp == n && s == "") || (temp < n && stringToInt(s) * Pow10(numDigits(temp)) + temp == n) // Corrected invariant
      decreases temp
    {
      s := (temp % 10 as char + '0' as char) + s;
      temp := temp / 10;
    }
    s
}

// Helper function to calculate the number of digits in an integer
function numDigits(n: int): int
  requires n >= 0
{
  if n == 0 then 1 // 0 has one digit
  else
    var count := 0;
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant count >= 0
      decreases temp
    {
      temp := temp / 10;
      count := count + 1;
    }
    count
}

function split(s: string, separator: char): seq<string>
  ensures forall i :: 0 <= i < |split(s, separator)| ==> |split(s, separator)[i]| <= |s|
  ensures forall i :: 0 <= i < |split(s, separator)| ==>
            forall j :: 0 <= j < |split(s, separator)[i]| ==> split(s, separator)[i][j] != separator
{
  var result: seq<string> := [];
  var currentSegment := "";
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |currentSegment| ==> currentSegment[k] != separator
    invariant forall r :: 0 <= r < |result| ==> forall k :: 0 <= k < |result[r]| ==> result[r][k] != separator
    invariant string.Join("", result) + currentSegment == s[..i]
  {
    if i < |s| && s[i] != separator {
      currentSegment := currentSegment + s[i];
    } else {
      result := result + [currentSegment];
      currentSegment := "";
    }
  }
  return result
}

function replace(s: string, old: string, new: string): string
  requires |old| > 0
  ensures |replace(s, old, new)| >= 0
{
  var result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
  {
    if i + |old| <= |s| && s[i .. i + |old|] == old {
      result := result + new;
      i := i + |old|;
    } else {
      result := result + s[i .. i + 1];
      i := i + 1;
    }
  }
  return result;
}

predicate isValidInteger(s: string)
{
  |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
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
  var cleanedInput := replace(input, "\n", "");
  var parts := split(cleanedInput, ' ');
  var trainFare := stringToInt(parts[0]);
  var busFare := stringToInt(parts[1]);

  var totalCost := TotalCost(trainFare, busFare);
  result := intToString(totalCost) + "\n";
}
// </vc-code>

