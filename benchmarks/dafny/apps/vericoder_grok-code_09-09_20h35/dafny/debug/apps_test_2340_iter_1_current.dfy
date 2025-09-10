predicate ValidInput(h: int, n: int, platforms: seq<int>)
{
    h >= 1 && n >= 1 && |platforms| >= n && n > 0 && platforms[0] == h
}

predicate ValidCrystalCount(crystals: int, n: int)
{
    crystals >= 0 && crystals <= n - 1
}

function CountCrystalsNeeded(h: int, platforms: seq<int>): int
  requires |platforms| >= 1
  requires platforms[0] == h
  requires h >= 1
{
    if |platforms| == 1 then 0
    else CountCrystalsNeededUpTo(h, platforms + [0], |platforms| - 1)
}

function CountCrystalsNeededUpTo(h: int, arr: seq<int>, upTo: int): int
  requires |arr| >= 1
  requires 0 <= upTo < |arr|
  requires arr[0] == h
  requires h >= 1
  decreases upTo
{
    if upTo == 0 then 0
    else
        var curPos := SimulatePositionUpTo(h, arr, upTo - 1);
        var prevCrystals := CountCrystalsNeededUpTo(h, arr, upTo - 1);
        if curPos == arr[upTo] then prevCrystals
        else if upTo + 1 < |arr| && arr[upTo + 1] == arr[upTo] - 1 then prevCrystals
        else prevCrystals + 1
}

function SimulatePositionUpTo(h: int, arr: seq<int>, upTo: int): int
  requires |arr| >= 1
  requires 0 <= upTo < |arr|
  requires arr[0] == h
  requires h >= 1
  decreases upTo
{
    if upTo == 0 then h
    else
        var prevPos := SimulatePositionUpTo(h, arr, upTo - 1);
        if prevPos == arr[upTo] then prevPos
        else if upTo + 1 < |arr| && arr[upTo + 1] == arr[upTo] - 1 then arr[upTo] - 1
        else prevPos
}

// <vc-helpers>
function CharToInt(c: char): int
{
  (int)c - 48
}

function AllDigits(s: string): bool
{
  forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToInt(s: string): int
  requires AllDigits(s) && |s| > 0
{
  if |s| == 1 then CharToInt(s[0])
  else 10 * StringToInt(s[0..|s|-1]) + CharToInt(s[|s|-1])
}

function SplitBySpaceAux(input: seq<char>, current: string, result: seq<string>): seq<string>
  decreases |input|
{
  if |input| == 0 then
    if |current| > 0 then result + [current] else result
  else
    if input[0] == ' ' then
      if |current| > 0 then SplitBySpaceAux(input[1..], [], result + [current])
      else SplitBySpaceAux(input[1..], [], result)
    else
      SplitBySpaceAux(input[1..], current + [input[0]], result)
}

function SplitBySpace(input: string): seq<string>
{
  SplitBySpaceAux(input, [], [])
}

function IntToStringRec(n: int, acc: seq<char>): seq<char>
  requires n >= 0
  decreases n
{
  if n == 0 then acc
  else IntToStringRec(n / 10, [(char)(48 + (n % 10))] + acc)
}

function IntToString(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else IntToStringRec(n / 10, [(char)(48 + (n % 10))])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
  var parts := SplitBySpace(input);
  var h := StringToInt(parts[0]);
  var n := StringToInt(parts[1]);
  var platforms: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |platforms| == i
  {
    platforms := platforms + [StringToInt(parts[2 + i])];
    i := i + 1;
  }
  if |parts| != 2 + n || platforms[0] != h || !ValidInput(h, n, platforms) {
    "invalid"
  } else {
    var count := CountCrystalsNeeded(h, platforms);
    IntToString(count)
  }
}
// </vc-code>

