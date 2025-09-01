function ParenthesesDepth(s: string, i: int, j: int): int
    decreases j - i 
    requires 0 <= i <= j <= |s|
{
    if i == j then
        0
    else if s[i] == '(' then
        ParenthesesDepth(s, i+1, j) + 1
    else if s[i] == ')' then
        ParenthesesDepth(s, i+1, j) - 1
    else
        ParenthesesDepth(s, i+1, j)
}
function InnerDepthsPositive(s: string) : bool
{
    forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) > 0
}
function InnerDepthsNonnegative(s: string) : bool
{
    forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) >= 0
}

// <vc-helpers>
// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method separate_paren_groups(paren_string: string) returns (res : seq<string>)
    // pre-conditions-start
    requires ParenthesesDepth(paren_string, 0, |paren_string|) == 0
    requires InnerDepthsNonnegative(paren_string)
    // pre-conditions-end
    // post-conditions-start
    ensures forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
    ensures forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var resSeq : seq<string> := [];
  var i := 0;
  while i < |paren_string| decreases |paren_string| - i
    invariant 0 <= i <= |paren_string|
    invariant forall k :: 0 <= k < |resSeq| ==> ParenthesesDepth(resSeq[k], 0, |resSeq[k]|) == 0
    invariant forall k :: 0 <= k < |resSeq| ==> InnerDepthsPositive(resSeq[k])
  {
    var depth := 0;
    var start := i;
    var pos := i;
    while pos < |paren_string| decreases |paren_string| - pos
      invariant 0 <= i <= pos <= |paren_string|
      invariant start == i
    {
      if paren_string[pos] == '(' {
        depth := depth + 1;
      } else if paren_string[pos] == ')' {
        depth := depth - 1;
      }
      pos := pos + 1;
      if depth == 0 {
        break;
      }
    }
    if pos != start {
      resSeq := resSeq + [paren_string[start..pos]];
    }
    i := pos;
  }
  res := resSeq;
}
// </vc-code>

