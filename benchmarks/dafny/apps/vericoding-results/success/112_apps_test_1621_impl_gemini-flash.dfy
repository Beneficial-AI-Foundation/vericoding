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
function sumSeq(s: seq<int>): int
  // `w` was an unbound identifier, and there's no obvious reason for sumSeq to read it.
  // The sumSeq function itself doesn't depend on any external mutable state `w`.
  // If `w` was intended to be a parameter, it wasn't declared.
  // Given sumSeq's simple recursive definition over a sequence,
  // `reads this` or no `reads` clause at all would be more appropriate if it were
  // part of a class and accessing class fields.
  // For a standalone function, no `reads` clause is needed for pure functions
  // that don't access ghost state or modify anything.
  // Removed `reads w`0` as it's not relevant here.
  decreases |s|
{
  if |s| == 0 then 0
  else s[0] + sumSeq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int, w: seq<int>) returns (result: int)
  requires ValidInput(s, k, w)
  ensures result == stringValue(s, w) + appendValue(|s|, k, maxValue(w))
// </vc-spec>
// <vc-code>
{
    var stringVal: int := stringValue(s, w);
    var maxVal: int := maxValue(w);
    var appendVal: int := appendValue(|s|, k, maxVal);
    result := stringVal + appendVal;
}
// </vc-code>

