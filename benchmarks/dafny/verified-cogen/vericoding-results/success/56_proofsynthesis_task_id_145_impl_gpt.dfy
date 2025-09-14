// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a >= b then a else b }
function min(a: int, b: int): int { if a <= b then a else b }

function MaxSeq(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] else max(s[0], MaxSeq(s[1..]))
}

function MinSeq(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] else min(s[0], MinSeq(s[1..]))
}

lemma ElemLeMax(s: seq<int>, k: int)
  requires |s| > 0
  requires 0 <= k < |s|
  ensures s[k] <= MaxSeq(s)
  decreases |s|
{
  if |s| == 1 {
  } else {
    if k == 0 {
    } else {
      assert |s[1..]| == |s| - 1;
      assert 0 <= k - 1 < |s[1..]|;
      ElemLeMax(s[1..], k - 1);
      assert s[1..][k - 1] == s[k];
    }
  }
}

lemma MinLeElem(s: seq<int>, k: int)
  requires |s| > 0
  requires 0 <= k < |s|
  ensures MinSeq(s) <= s[k]
  decreases |s|
{
  if |s| == 1 {
  } else {
    if k == 0 {
    } else {
      assert |s[1..]| == |s| - 1;
      assert 0 <= k - 1 < |s[1..]|;
      MinLeElem(s[1..], k - 1);
      assert s[1..][k - 1] == s[k];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method MaxDifference(arr: array<int>) returns (diff: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] - arr[j] <= diff
// </vc-spec>
// <vc-code>
{
  var s := arr[..];
  assert |s| == arr.Length;
  diff := MaxSeq(s) - MinSeq(s);
  forall i, j | 0 <= i < arr.Length && 0 <= j < arr.Length
    ensures arr[i] - arr[j] <= diff
  {
    assert 0 <= i < |s|;
    assert 0 <= j < |s|;
    assert s[i] == arr[i];
    assert s[j] == arr[j];
    ElemLeMax(s, i);
    MinLeElem(s, j);
  }
}
// </vc-code>
