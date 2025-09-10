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
lemma AppendValueLemma(startPos: int, count: int, maxVal: int)
  requires startPos >= 0
  requires count >= 0
  ensures appendValue(startPos, count, maxVal) == if count == 0 then 0 else maxVal * (startPos * count + (count * (count + 1)) / 2)
{
  if count == 0 {
    // Base case
  } else {
    AppendValueLemma(startPos, count - 1, maxVal);
    // Calculate the difference
    calc {
      appendValue(startPos, count, maxVal);
      == // by definition
      (startPos + count) * maxVal + appendValue(startPos, count - 1, maxVal);
      == { AppendValueLemma(startPos, count - 1, maxVal); }
      (startPos + count) * maxVal + maxVal * (startPos * (count - 1) + ((count - 1) * count) / 2);
      == 
      maxVal * (startPos + count + startPos * (count - 1) + ((count - 1) * count) / 2);
      ==
      maxVal * (startPos * count + count + ((count - 1) * count) / 2);
      ==
      maxVal * (startPos * count + (2 * count + (count - 1) * count) / 2);
      ==
      maxVal * (startPos * count + (count * (count + 1)) / 2);
    }
  }
}

lemma MaxValueInRange(w: seq<int>, i: int)
  requires |w| > 0
  requires 0 <= i < |w|
  ensures w[i] <= maxValue(w)
  decreases |w|
{
  if |w| == 1 {
    assert i == 0;
    assert maxValue(w) == w[0];
  } else {
    if w[0] >= maxValue(w[1..]) {
      assert maxValue(w) == w[0];
      if i == 0 {
      } else {
        assert 0 <= i-1 < |w[1..]|;  // This assertion holds because i >= 1 and |w| >= 2
        MaxValueInRange(w[1..], i-1);
        assert w[i] == w[1..][i-1];
        assert w[1..][i-1] <= maxValue(w[1..]);
        assert maxValue(w[1..]) <= w[0];
      }
    } else {
      assert maxValue(w) == maxValue(w[1..]);
      if i == 0 {
        assert w[0] <= maxValue(w[1..]);
      } else {
        assert 0 <= i-1 < |w[1..]|;  // This assertion holds because i >= 1 and |w| >= 2
        MaxValueInRange(w[1..], i-1);
      }
    }
  }
}

lemma MaxValueNonEmpty(w: seq<int>)
  requires |w| > 0
  ensures forall i :: 0 <= i < |w| ==> w[i] <= maxValue(w)
{
  var i := 0;
  while i < |w|
    invariant 0 <= i <= |w|
    invariant forall j :: 0 <= j < i ==> w[j] <= maxValue(w)
  {
    MaxValueInRange(w, i);
    i := i + 1;
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
  var maxVal := maxValue(w);
  result := stringValue(s, w);
  
  if k > 0 {
    var n := |s|;
    MaxValueNonEmpty(w);
    AppendValueLemma(n, k, maxVal);
    result := result + maxVal * (n * k + (k * (k + 1)) / 2);
  }
}
// </vc-code>

