function stringValue(s: string, w: seq<int>): int
  requires |w| == 26
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
{
  if |s| == 0 then 0
  else
    var charIndex := (s[|s|-1] as int) - ('a' as int);
    stringValue(s[..|s|-1], w) + |s| * w[charIndex]
}

function appendValue(startPos: int, count: int, maxVal: int): int
  requires startPos >= 0
  requires count >= 0
{
  if count == 0 then 0
  else (startPos + count) * maxVal + appendValue(startPos, count - 1, maxVal)
}

function maxValue(w: seq<int>): int
  requires |w| > 0
  ensures exists i :: 0 <= i < |w| && maxValue(w) == w[i]
  ensures forall i :: 0 <= i < |w| ==> w[i] <= maxValue(w)
{
  if |w| == 1 then w[0]
  else if w[0] >= maxValue(w[1..]) then w[0]
  else maxValue(w[1..])
}

predicate ValidInput(s: string, k: int, w: seq<int>)
{
  |w| == 26 && 
  k >= 0 && 
  |s| <= 1000 && 
  k <= 1000 && 
  (forall i :: 0 <= i < |w| ==> 0 <= w[i] <= 1000) &&
  (forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z')
}

// <vc-helpers>
lemma MaxValueIsElement(w: seq<int>)
  requires |w| > 0
  ensures exists i :: 0 <= i < |w| && maxValue(w) == w[i]
  decreases |w|
{
  if |w| == 1 {
    assert maxValue(w) == w[0];
    assert 0 <= 0 < |w| && maxValue(w) == w[0];
  } else {
    if w[0] >= maxValue(w[1..]) {
      assert maxValue(w) == w[0];
      assert 0 <= 0 < |w| && maxValue(w) == w[0];
    } else {
      MaxValueIsElement(w[1..]);
      var i :| 0 <= i < |w[1..]| && maxValue(w[1..]) == w[1..][i];
      assert w[1..][i] == w[i+1];
      assert maxValue(w) == maxValue(w[1..]);
      assert 0 <= i+1 < |w| && maxValue(w) == w[i+1];
    }
  }
}

lemma StringValueNonNegative(s: string, w: seq<int>)
  requires |w| == 26
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  requires forall i :: 0 <= i < |w| ==> 0 <= w[i] <= 1000
  ensures stringValue(s, w) >= 0
  decreases |s|
{
  if |s| == 0 {
    assert stringValue(s, w) == 0;
  } else {
    var charIndex := (s[|s|-1] as int) - ('a' as int);
    assert 0 <= charIndex < 26;
    StringValueNonNegative(s[..|s|-1], w);
    assert stringValue(s[..|s|-1], w) >= 0;
    assert |s| > 0;
    assert w[charIndex] >= 0;
    assert |s| * w[charIndex] >= 0;
    assert stringValue(s, w) == stringValue(s[..|s|-1], w) + |s| * w[charIndex];
    assert stringValue(s, w) >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int, w: seq<int>) returns (result: int)
  requires ValidInput(s, k, w)
  ensures result == stringValue(s, w) + appendValue(|s|, k, maxValue(w))
// </vc-spec>
// <vc-code>
{
  MaxValueIsElement(w);
  StringValueNonNegative(s, w);
  
  var stringVal := stringValue(s, w);
  var maxW := maxValue(w);
  var appendVal := appendValue(|s|, k, maxW);
  result := stringVal + appendVal;
}
// </vc-code>

