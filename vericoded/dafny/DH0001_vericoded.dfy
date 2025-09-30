// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
lemma DepthAdditivity(s: string, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= |s|
    ensures ParenthesesDepth(s, i, k) == ParenthesesDepth(s, i, j) + ParenthesesDepth(s, j, k)
    decreases j - i
{
    if i == j {
    } else {
        DepthAdditivity(s, i + 1, j, k);
    }
}

lemma SubstrDepth(s: string, start: int, end: int, i: int, j: int)
    requires 0 <= start <= end <= |s|
    requires 0 <= i <= j <= end - start
    ensures ParenthesesDepth(s[start..end], i, j) == ParenthesesDepth(s, start + i, start + j)
    decreases j - i
{
    if i == j {
    } else {
        var sub := s[start..end];
        assert s[start+i] == sub[i];
        SubstrDepth(s, start, end, i + 1, j);
    }
}

lemma ProveInnerDepthsPositive(s: string, start: int, end: int)
    requires 0 <= start < end <= |s|
    requires ParenthesesDepth(s, start, end) == 0
    requires forall j :: start < j < end ==> ParenthesesDepth(s, start, j) > 0
    ensures InnerDepthsPositive(s[start..end])
{
    var sub := s[start..end];
    forall k | 0 < k < |sub|
        ensures ParenthesesDepth(sub, 0, k) > 0
    {
        SubstrDepth(s, start, end, 0, k);
        var j := start + k;
        assert start < j < end;
    }
}
// </vc-helpers>

// <vc-spec>
method separate_paren_groups(paren_string: string) returns (res : seq<string>)

    requires ParenthesesDepth(paren_string, 0, |paren_string|) == 0
    requires InnerDepthsNonnegative(paren_string)

    ensures forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
    ensures forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): added SubstrDepth call to prove loop invariant */
  res := [];
  var start := 0;
  var i := 0;
  while i < |paren_string|
    invariant 0 <= start <= i <= |paren_string|
    invariant ParenthesesDepth(paren_string, 0, start) == 0
    invariant forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
    invariant forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
    invariant forall j :: start < j <= i ==> ParenthesesDepth(paren_string, 0, j) != 0
    decreases |paren_string| - i
  {
    if ParenthesesDepth(paren_string, 0, i + 1) == 0 {
      var group := paren_string[start..i+1];

      DepthAdditivity(paren_string, 0, start, i + 1);
      SubstrDepth(paren_string, start, i + 1, 0, |group|);

      forall j | start < j < i + 1
        ensures ParenthesesDepth(paren_string, start, j) > 0
      {
        DepthAdditivity(paren_string, 0, start, j);
      }

      ProveInnerDepthsPositive(paren_string, start, i + 1);

      res := res + [group];
      start := i + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
