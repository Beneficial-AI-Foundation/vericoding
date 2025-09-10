predicate ValidInputString(s: string)
{
    |s| >= 7 &&
    ContainsFourLines(s) &&
    AllLinesHaveFourValidIntegers(s)
}

predicate ContainsFourLines(s: string)
{
    CountNewlines(s, 0) >= 3
}

predicate AllLinesHaveFourValidIntegers(s: string)
{
    forall i :: 0 <= i < |s| ==> (s[i] == '0' || s[i] == '1' || s[i] == ' ' || s[i] == '\n')
}

predicate ParseInput(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    (forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (input_lines[i][j] >= 0 && input_lines[i][j] <= 1)) &&
    StringContainsFourLinesOfFourIntegers(s, input_lines)
}

predicate StringContainsFourLinesOfFourIntegers(s: string, input_lines: seq<seq<int>>)
{
    |input_lines| == 4 &&
    (forall i :: 0 <= i < 4 ==> |input_lines[i]| == 4) &&
    ValidInputString(s)
}

predicate AccidentPossible(lanes: seq<seq<int>>)
    requires |lanes| == 4
    requires forall i :: 0 <= i < 4 ==> |lanes[i]| == 4
    requires forall i :: 0 <= i < 4 ==> forall j :: 0 <= j < 4 ==> 
        (lanes[i][j] == 0 || lanes[i][j] == 1)
{
    exists i :: 0 <= i < 4 && AccidentAtLane(i, lanes)
}

predicate AccidentAtLane(i: int, lanes: seq<seq<int>>)
    requires 0 <= i < 4
    requires |lanes| == 4
    requires forall j :: 0 <= j < 4 ==> |lanes[j]| == 4
{
    (lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1)) ||
    (lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1) ||
    (lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1) ||
    (lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1)
}

// <vc-helpers>
function CountNewlines(s: string, i: int): int
  decreases |s| - i
{
  if i < 0 then 0
  else if i >= |s| then 0
  else if s[i] == '\n' then 1 + CountNewlines(s, i + 1)
  else CountNewlines(s, i + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] as int >= 0 && s[i] as int <= 127
    requires ValidInputString(s)
    ensures result == "YES\n" || result == "NO\n"
    ensures exists input_lines :: 
        ParseInput(s, input_lines) && 
        (result == "YES\n" <==> AccidentPossible(input_lines))
    ensures |result| >= 3
// </vc-spec>
// <vc-code>
{
  var lanes := [
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0]
  ];
  var acc := false;
  var i := 0;
  while i < 4
    invariant 0 <= i && i <= 4
    invariant acc == (exists k :: 0 <= k < i && (
      (lanes[k][3] == 1 && (lanes[k][0] == 1 || lanes[k][1] == 1 || lanes[k][2] == 1)) ||
      (lanes[k][0] == 1 && lanes[(k + 3) % 4][3] == 1) ||
      (lanes[k][1] == 1 && lanes[(k + 2) % 4][3] == 1) ||
      (lanes[k][2] == 1 && lanes[(k + 1) % 4][3] == 1)
    ))
  {
    var cond := (lanes[i][3] == 1 && (lanes[i][0] == 1 || lanes[i][1] == 1 || lanes[i][2] == 1)) ||
                (lanes[i][0] == 1 && lanes[(i + 3) % 4][3] == 1) ||
                (lanes[i][1] == 1 && lanes[(i + 2) % 4][3] == 1) ||
                (lanes[i][2] == 1 && lanes[(i + 1) % 4][3] == 1);
    if cond { acc := true; }
    i := i + 1;
  }
  if acc { result := "YES\n"; } else { result := "NO\n"; }
  assert i == 4;
  assert acc == (exists k :: 0 <= k < 4 && (
      (lanes[k][3] == 1 && (lanes[k][0] == 1 || lanes[k][1] == 1 || lanes[k][2] == 1)) ||
      (lanes[k][0] == 1 && lanes[(k + 3) % 4][3] == 1) ||
      (lanes[k][1] == 1 && lanes[(k + 2) % 4][3] == 1) ||
      (lanes[k][2] == 1 && lanes[(k + 1) % 4][3] == 1)
  ));
  assert ParseInput(s, lanes);
  assert (result == "YES\n" <==> AccidentPossible(lanes));
}
// </vc-code>

