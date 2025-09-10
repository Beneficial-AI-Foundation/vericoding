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
function SplitString(input: string): seq<string>
  ensures forall i :: 0 <= i < |SplitString(input)| ==> |SplitString(input)[i]| > 0
{
  if input == "" then
    []
  else
    var parts: seq<string> := [];
    var currentPart := "";
    var i := 0;
    while i < |input|
      invariant 0 <= i <= |input|
      invariant forall k :: 0 <= k < |parts| ==> |parts[k]| > 0
      invariant forall k :: 0 <= k < |currentPart| ==> currentPart[k] != ' '
    {
      if input[i] == ' '
      {
        if currentPart != ""
        {
          parts := parts + [currentPart];
        }
        currentPart := "";
      } else {
        currentPart := currentPart + [input[i]];
      }
      i := i + 1;
    }
    if currentPart != ""
    {
      parts := parts + [currentPart];
    }
    parts
}

function StringToInt(s: string): (i: int)
  requires |s| > 0
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  ensures i >= 0
{
  var res := 0;
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant res >= 0
    invariant forall l :: 0 <= l < k ==> '0' <= s[l] <= '9'
  {
    res := res * 10 + (s[k] as int - '0' as int);
    k := k + 1;
  }
  res
}

function ParseInput(input: string): (h: int, n: int, platforms: seq<int>)
  requires |input| > 0
  ensures h >= 1 && n >= 1
  ensures |platforms| >= n
  ensures platforms[0] == h
  ensures n > 0
{
  var parts := SplitString(input);
  assert |parts| >= 2; // At least h and n are present.
  var h_str := parts[0];
  var n_str := parts[1];

  var h_val := StringToInt(h_str);
  var n_val := StringToInt(n_str);

  var platform_seq: seq<int> := [];
  var i := 2;
  while i < |parts|
    invariant 2 <= i <= |parts|
    invariant forall k :: 0 <= k < |platform_seq| ==> platform_seq[k] >= 0 // Platforms values must be non-negative.
  {
    platform_seq := platform_seq + [StringToInt(parts[i])];
    i := i + 1;
  }
  (h_val, n_val, platform_seq)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
    var h: int;
    var n: int;
    var platforms: seq<int>;
    (h, n, platforms) := ParseInput(input);

    if !ValidInput(h, n, platforms) then
        return "Invalid Input";

    var crystalsNeeded := CountCrystalsNeeded(h, platforms);

    if !ValidCrystalCount(crystalsNeeded, n) then
        return "Invalid Crystal Count Result";

    return crystalsNeeded as string;
}
// </vc-code>

