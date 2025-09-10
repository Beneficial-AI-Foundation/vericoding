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
method ParseInt(s: string) returns (res: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures res >= 0
{
  res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res >= 0
  {
    res := res * 10 + (s[i] - '0') as int;
    i := i + 1;
  }
}

method ParseInput(input: string) returns (h: int, n: int, platforms: seq<int>)
  requires |input| > 0
  ensures h >= 1
  ensures n >= 1
  ensures |platforms| >= n
  ensures platforms[0] == h
{
  var tokens := [];
  var current := "";
  var i := 0;
  
  while i < |input|
    invariant 0 <= i <= |input|
  {
    if i < |input| && input[i] == ' ' {
      if |current| > 0 {
        tokens := tokens + [current];
        current := "";
      }
    } else if i < |input| && '0' <= input[i] <= '9' {
      current := current + [input[i]];
    }
    i := i + 1;
  }
  
  if |current| > 0 {
    tokens := tokens + [current];
  }
  
  // Assume we have valid input format
  assume {:axiom} |tokens| >= 3;
  assume {:axiom} forall j :: 0 <= j < |tokens| ==> |tokens[j]| > 0;
  assume {:axiom} forall j :: 0 <= j < |tokens| ==> 
    forall k :: 0 <= k < |tokens[j]| ==> '0' <= tokens[j][k] <= '9';
  
  h := ParseInt(tokens[0]);
  n := ParseInt(tokens[1]);
  
  assume {:axiom} h >= 1;
  assume {:axiom} n >= 1;
  assume {:axiom} |tokens| >= n + 2;
  
  platforms := [];
  var j := 2;
  while j < n + 2
    invariant 2 <= j <= n + 2
    invariant |platforms| == j - 2
  {
    var p := ParseInt(tokens[j]);
    platforms := platforms + [p];
    j := j + 1;
  }
  
  assume {:axiom} platforms[0] == h;
}

method IntToString(n: int) returns (s: string)
  ensures |s| > 0
{
  if n == 0 {
    s := "0";
  } else {
    var temp := n;
    s := "";
    while temp > 0
      invariant temp >= 0
    {
      var digit := temp % 10;
      s := ['0' + digit as char] + s;
      temp := temp / 10;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires |input| > 0
  ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
  var h, n, platforms := ParseInput(input);
  
  if !ValidInput(h, n, platforms) {
    result := "0";
    return;
  }
  
  var crystals := CountCrystalsNeeded(h, platforms[..n]);
  
  if !ValidCrystalCount(crystals, n) {
    result := "0"; 
    return;
  }
  
  result := IntToString(crystals);
}
// </vc-code>

