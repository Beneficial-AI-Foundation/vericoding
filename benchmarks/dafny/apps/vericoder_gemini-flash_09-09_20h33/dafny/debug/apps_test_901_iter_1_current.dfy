function SplitLines(s: string): seq<string>
    requires |s| >= 0
    ensures |SplitLines(s)| >= 0
    ensures |s| == 0 ==> |SplitLines(s)| == 0
    ensures |s| > 0 ==> |SplitLines(s)| >= 1
    ensures forall i :: 0 <= i < |SplitLines(s)| ==> |SplitLines(s)[i]| >= 0
{
    if |s| == 0 then [] else [s]
}

function SplitInts(s: string): seq<int>
    requires |s| >= 0
    ensures |SplitInts(s)| >= 0
{
    []
}

function SeqToSet(s: seq<int>): set<int>
{
    set x | x in s
}

function is_dangerous_group(group_data: seq<int>): bool
{
    if |group_data| <= 1 then false
    else
        var group_members := group_data[1..];
        var member_set := SeqToSet(group_members);
        forall member :: member in member_set ==> -member !in member_set
}

predicate exists_dangerous_group(stdin_input: string)
    requires |stdin_input| > 0
{
    var lines := SplitLines(stdin_input);
    if |lines| == 0 then false
    else
        var first_line := SplitInts(lines[0]);
        if |first_line| < 2 then false
        else
            var n := first_line[0];
            var m := first_line[1];
            if m <= 0 || n <= 0 then false
            else
                exists i :: 1 <= i <= m && i < |lines| && 
                    is_dangerous_group(SplitInts(lines[i]))
}

// <vc-helpers>
function method ParseInt(s: string): (i: int)
  requires |s| > 0
  requires forall c :: c in s ==> '0' <= c <= '9'
  ensures i >= 0
{
  if |s| == 1 then
    (s[0] as int) - ('0' as int)
  else
    (ParseInt(s[..|s|-1]) * 10) + ((s[|s|-1] as int) - ('0' as int))
}

function method StringToInt(s: string, start: int, end: int): int
  requires 0 <= start <= end <= |s|
  requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
  ensures StringToInt(s, start, end) >= 0
{
  if start == end then 0
  else ParseInt(s[start..end])
}

function method SplitOnSpace(s: string): seq<string>
  ensures forall x :: x in SplitOnSpace(s) ==> |x| > 0
{
  var result := new seq<string>();
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x :: x in result ==> |x| > 0
  {
    while i < |s| && s[i] == ' '
    {
      i := i + 1;
    }
    var start := i;
    while i < |s| && s[i] != ' '
    {
      i := i + 1;
    }
    if start < i
    {
      result := result + [s[start..i]];
    }
  }
  return result
}

override function SplitLines(s: string): seq<string>
  requires |s| >= 0
  ensures |SplitLines(s)| >= 0
  ensures |s| == 0 ==> |SplitLines(s)| == 0
  ensures |s| > 0 ==> |SplitLines(s)| >= 1
  ensures forall i :: 0 <= i < |SplitLines(s)| ==> |SplitLines(s)[i]| >= 0
{
  if |s| == 0 then []
  else
    var result := new seq<string>();
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
    {
      var start := i;
      while i < |s| && s[i] != '\n'
      {
        i := i + 1;
      }
      result := result + [s[start..i]];
      if i < |s| && s[i] == '\n'
      {
        i := i + 1;
      }
    }
    return result
}

override function SplitInts(s: string): seq<int>
  requires |s| >= 0
  ensures |SplitInts(s)| >= 0
{
  var parts := SplitOnSpace(s);
  var result := new seq<int>(|parts|);
  for i := 0 to |parts| - 1
    ensures |result| == |parts|
    ensures forall j :: 0 <= j < i ==> result[j] == StringToInt(parts[j], 0, |parts[j]|)
  {
    result[i] := StringToInt(parts[i], 0, |parts[i]|);
  }
  return result
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures result == "YES\n" || result == "NO\n"
    ensures (result == "YES\n") <==> exists_dangerous_group(stdin_input)
    ensures (result == "NO\n") <==> !exists_dangerous_group(stdin_input)
// </vc-spec>
// <vc-code>
{
    if exists_dangerous_group(stdin_input) then
        result := "YES\n"
    else
        result := "NO\n"
}
// </vc-code>

