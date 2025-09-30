// <vc-preamble>

function SplitBySpacesResult(s: string): seq<string>
    requires forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    ensures forall i :: 0 <= i < |SplitBySpacesResult(s)| ==> forall j :: 0 <= j < |SplitBySpacesResult(s)[i]| ==> SplitBySpacesResult(s)[i][j] == '(' || SplitBySpacesResult(s)[i][j] == ')'
    ensures |s| == 0 ==> |SplitBySpacesResult(s)| == 0
{
    if |s| == 0 then []
    else
        var groups := [];
        var current_group := "";
        var i := 0;
        SplitBySpacesHelper(s, i, current_group, groups)
}

function MaxNestingDepth(group: string): int
    requires forall i :: 0 <= i < |group| ==> group[i] == '(' || group[i] == ')'
    ensures MaxNestingDepth(group) >= 0
{
    MaxNestingDepthHelper(group, 0, 0, 0)
}

function SplitBySpacesHelper(s: string, i: int, current_group: string, groups: seq<string>): seq<string>
    requires 0 <= i <= |s|
    requires forall k :: 0 <= k < |s| ==> s[k] == '(' || s[k] == ')' || s[k] == ' '
    requires forall k :: 0 <= k < |groups| ==> forall j :: 0 <= j < |groups[k]| ==> groups[k][j] == '(' || groups[k][j] == ')'
    requires forall j :: 0 <= j < |current_group| ==> current_group[j] == '(' || current_group[j] == ')'
    ensures forall k :: 0 <= k < |SplitBySpacesHelper(s, i, current_group, groups)| ==> forall j :: 0 <= j < |SplitBySpacesHelper(s, i, current_group, groups)[k]| ==> SplitBySpacesHelper(s, i, current_group, groups)[k][j] == '(' || SplitBySpacesHelper(s, i, current_group, groups)[k][j] == ')'
    decreases |s| - i
{
    if i == |s| then
        if |current_group| > 0 then groups + [current_group] else groups
    else if s[i] == ' ' then
        if |current_group| > 0 then
            SplitBySpacesHelper(s, i + 1, "", groups + [current_group])
        else
            SplitBySpacesHelper(s, i + 1, current_group, groups)
    else
        SplitBySpacesHelper(s, i + 1, current_group + [s[i]], groups)
}

function MaxNestingDepthHelper(group: string, index: int, current_depth: int, max_depth: int): int
    requires 0 <= index <= |group|
    requires max_depth >= 0
    decreases |group| - index
    ensures MaxNestingDepthHelper(group, index, current_depth, max_depth) >= 0
{
    if index == |group| then max_depth
    else if group[index] == '(' then
        var new_current := current_depth + 1;
        var new_max := if new_current > max_depth then new_current else max_depth;
        MaxNestingDepthHelper(group, index + 1, new_current, new_max)
    else if group[index] == ')' then
        MaxNestingDepthHelper(group, index + 1, current_depth - 1, max_depth)
    else
        MaxNestingDepthHelper(group, index + 1, current_depth, max_depth)
}

method SplitBySpaces(s: string) returns (groups: seq<string>)
    requires forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    ensures forall i :: 0 <= i < |groups| ==> ' ' !in groups[i]
    ensures forall i :: 0 <= i < |groups| ==> forall j :: 0 <= j < |groups[i]| ==> groups[i][j] == '(' || groups[i][j] == ')'
    ensures |s| == 0 ==> |groups| == 0
    ensures groups == SplitBySpacesResult(s)
{
    groups := [];
    var current_group := "";

    if |s| == 0 {
        return;
    }

    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant ' ' !in current_group
        invariant forall k :: 0 <= k < |groups| ==> ' ' !in groups[k]
        invariant forall k :: 0 <= k < |groups| ==> forall j :: 0 <= j < |groups[k]| ==> groups[k][j] == '(' || groups[k][j] == ')'
        invariant forall j :: 0 <= j < |current_group| ==> current_group[j] == '(' || current_group[j] == ')'
        invariant SplitBySpacesResult(s) == SplitBySpacesHelper(s, i, current_group, groups)
    {
        if s[i] == ' ' {
            if |current_group| > 0 {
                groups := groups + [current_group];
                current_group := "";
            }
        } else {
            current_group := current_group + [s[i]];
        }
        i := i + 1;
    }

    if |current_group| > 0 {
        groups := groups + [current_group];
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method parse_nested_parens(paren_string: string) returns (result: seq<int>)
    requires forall i :: 0 <= i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '
    ensures |result| == |SplitBySpacesResult(paren_string)|
    ensures forall i :: 0 <= i < |result| ==> result[i] >= 0
    ensures |paren_string| == 0 ==> |result| == 0
    ensures forall i :: 0 <= i < |result| ==> result[i] == MaxNestingDepth(SplitBySpacesResult(paren_string)[i])
// </vc-spec>
// <vc-code>
{
  var groups := SplitBySpaces(paren_string);
  result := [];
  var i := 0;
  while i < |groups|
    invariant 0 <= i <= |groups|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == MaxNestingDepth(groups[j])
    invariant forall j :: 0 <= j < i ==> result[j] >= 0
    invariant groups == SplitBySpacesResult(paren_string)
  {
    var depth := MaxNestingDepth(groups[i]);
    result := result + [depth];
    i := i + 1;
  }
}
// </vc-code>
