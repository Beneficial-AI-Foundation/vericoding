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
// No helper code required for this solution.
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
  var s := input;
  var L := |s|;
  var i := 0;
  var nums: seq<int> := [];
  while i < L
    decreases L - i
  {
    var c := s[i];
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' {
      i := i + 1;
    } else {
      var sign := 1;
      if c == '-' {
        sign := -1;
        i := i + 1;
      }
      var started := false;
      var x := 0;
      while i < L && '0' <= s[i] && s[i] <= '9'
        decreases L - i
      {
        started := true;
        x := x * 10 + (s[i] - '0');
        i := i + 1;
      }
      if started {
        nums := nums + [sign * x];
      } else {
        // skip unexpected single non-space character
        i := i + 1;
      }
    }
  }

  // Default result if input malformed
  var out := "0";
  if |nums| >= 2 {
    var h := nums[0];
    var n := nums[1];
    if n >= 1 && |nums| >= 2 + n && nums[2] == h {
      var platforms := nums[2 .. 2 + n];
      // ensure preconditions for CountCrystalsNeeded hold before calling
      if h >= 1 && |platforms| >= 1 && platforms[0] == h {
        var crystals := CountCrystalsNeeded(h, platforms);
        out := crystals.ToString();
      }
    }
  }
  result := out;
}
// </vc-code>

