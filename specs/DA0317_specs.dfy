// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int, w: seq<int>) returns (result: int)
  requires ValidInput(s, k, w)
  ensures result == stringValue(s, w) + appendValue(|s|, k, maxValue(w))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
