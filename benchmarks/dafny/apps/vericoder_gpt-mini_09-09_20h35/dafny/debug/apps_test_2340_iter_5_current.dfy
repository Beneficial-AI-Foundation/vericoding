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
function Digit(c: char): int
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
  else if c == '9' then 9
  else 0
}

function DigitChar(d: int): string
  requires 0 <= d < 10
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else "9"
}

function IntToString(n: int): string
  requires n >= 0
  decreases n
{
  if n < 10 then DigitChar(n)
  else IntToString(n / 10) + DigitChar(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
  var s: string := input;
  var L: int := |s|;
  var i: int := 0;
  var nums: seq<int> := [];
  while i < L
    decreases L - i
  {
    var oldI := i;
    var c: char := s[i];
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' {
      i := i + 1;
    } else {
      var sign: int := 1;
      if c == '-' {
        sign := -1;
        i := i + 1;
      }
      var started: bool := false;
      var x: int := 0;
      var j: int := i;
      while j < L && '0' <= s[j] && s[j] <= '9'
        decreases L - j
        invariant j >= oldI
      {
        started := true;
        x := x * 10 + Digit(s[j]);
        j := j + 1;
      }
      if started {
        // ensure progress even if the verifier cannot deduce j > oldI
        if j > oldI {
          nums := nums + [sign * x];
          i := j;
        } else {
          nums := nums + [sign * x];
          i := oldI + 1;
        }
      } else {
        // skip unexpected single non-space character
        i := j + 1;
      }
    }
    assert i > oldI;
  }

  // Default result if input malformed
  var out: string := "0";
  if |nums| >= 2 {
    var h: int := nums[0];
    var n: int := nums[1];
    if n >= 1 && |nums| >= 2 + n && nums[2] == h {
      var platforms := nums[2 .. 2 + n];
      // ensure preconditions for CountCrystalsNeeded hold before calling
      if h >= 1 && |platforms| >= 1 && platforms[0] == h {
        var crystals := CountCrystalsNeeded(h, platforms);
        if crystals >= 0 {
          out := IntToString(crystals);
        }
      }
    }
  }
  result := out;
}
// </vc-code>

