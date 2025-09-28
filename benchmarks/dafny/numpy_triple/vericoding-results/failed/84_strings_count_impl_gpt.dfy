// <vc-preamble>
// Predicate to check if a substring occurs at a specific position in a string
predicate SubstringAt(s: string, sub: string, pos: int)
{
  pos >= 0 && pos + |sub| <= |s| && s[pos..pos + |sub|] == sub
}

// Predicate to check if positions are non-overlapping for a given substring length
predicate NonOverlapping(positions: seq<int>, subLen: int)
{
  forall i, j :: 0 <= i < j < |positions| ==> positions[i] + subLen <= positions[j]
}

// Predicate to check if all positions are valid matches within the range
predicate ValidMatches(s: string, sub: string, positions: seq<int>, start: int, endPos: int)
{
  forall pos :: pos in positions ==> 
    start <= pos && pos + |sub| <= endPos && SubstringAt(s, sub, pos)
}

// Predicate to check if a set of positions represents the maximum non-overlapping count
ghost predicate MaximalMatches(s: string, sub: string, positions: seq<int>, start: int, endPos: int)
{
  ValidMatches(s, sub, positions, start, endPos) &&
  NonOverlapping(positions, |sub|) &&
  forall otherPositions :: 
    |otherPositions| <= (endPos - start) &&
    (forall pos :: pos in otherPositions ==> start <= pos && pos + |sub| <= endPos) &&
    (ValidMatches(s, sub, otherPositions, start, endPos) && NonOverlapping(otherPositions, |sub|)) ==>
    |otherPositions| <= |positions|
}
// </vc-preamble>

// <vc-helpers>
function GreedyPositions(s: string, sub: string, start: int, endPos: int): seq<int>
  requires 0 <= start <= |s|
  requires 0 <= endPos <= |s|
  requires start <= endPos
  requires |sub| > 0
  decreases endPos - start
{
  if endPos - start < |sub| then []
  else if SubstringAt(s, sub, start) then
    [start] + GreedyPositions(s, sub, start + |sub|, endPos)
  else
    GreedyPositions(s, sub, start + 1, endPos)
}

function FilterGE(xs: seq<int>, cutoff: int): seq<int>
  decreases |xs|
{
  if |xs| == 0 then []
  else if xs[0] >= cutoff then [xs[0]] + FilterGE(xs[1..], cutoff)
  else FilterGE(xs[1..], cutoff)
}

lemma FilterGE_Subseq(xs: seq<int>, cutoff: int)
  ensures forall y :: y in FilterGE(xs, cutoff) ==> y in xs
{
  if |xs| == 0 {
  } else {
    FilterGE_Subseq(xs[1..], cutoff);
  }
}

lemma FilterGE_AllGE(xs: seq<int>, cutoff: int)
  ensures (forall i :: 0 <= i < |xs| ==> xs[i] >= cutoff) ==> FilterGE(xs, cutoff) == xs
{
  if |xs| == 0 {
  } else {
    FilterGE_AllGE(xs[1..], cutoff);
    if xs[0] >= cutoff {
    } else {
    }
  }
}

lemma TailNonOverlapping(xs: seq<int>, subLen: int)
  requires NonOverlapping(xs, subLen)
  ensures NonOverlapping(xs[1..], subLen)
{
}

lemma ValidMatchesShiftLeft(s: string, sub: string, positions: seq<int>, start: int, start': int, endPos: int)
  requires start <= start' <= endPos
  requires ValidMatches(s, sub, positions, start', endPos)
  ensures ValidMatches(s, sub, positions, start, endPos)
{
}

lemma FilterGE_Preserves(s: string, sub: string, xs: seq<int>, start: int, start': int, endPos: int)
  requires 0 <= start <= start' <= endPos
  requires ValidMatches(s, sub, xs, start, endPos)
  requires NonOverlapping(xs, |sub|)
  ensures ValidMatches(s, sub, FilterGE(xs, start'), start', endPos)
  ensures NonOverlapping(FilterGE(xs, start'), |sub|)
{
  if |xs| == 0 {
  } else {
    FilterGE_Preserves(s, sub, xs[1..], start, start', endPos);
  }
}

lemma NoPositionAtStartIfNoMatch(s: string, sub: string, positions: seq<int>, start: int, endPos: int)
  requires ValidMatches(s, sub, positions, start, endPos)
  requires !SubstringAt(s, sub, start)
  ensures forall i :: 0 <= i < |positions| ==> positions[i] >= start + 1
{
}

lemma LengthBoundWithFilter(s: string, sub: string, xs: seq<int>, start: int, endPos: int)
  requires ValidMatches(s, sub, xs, start, endPos)
  requires NonOverlapping(xs, |sub|)
  ensures |xs| <= 1 + |FilterGE(xs, start + |sub|)|
{
  if |xs| == 0 {
  } else {
    LengthBoundWithFilter(s, sub, xs[1..], start, endPos);
  }
}

lemma GreedyMaximal(s: string, sub: string, start: int, endPos: int)
  requires 0 <= start <= |s|
  requires 0 <= endPos <= |s|
  requires start <= endPos
  requires |sub| > 0
  ensures MaximalMatches(s, sub, GreedyPositions(s, sub, start, endPos), start, endPos)
  decreases endPos - start
{
  if endPos - start < |sub| {
  } else if SubstringAt(s, sub, start) {
    GreedyMaximal(s, sub, start + |sub|, endPos);
  } else {
    GreedyMaximal(s, sub, start + 1, endPos);
  }
}
// </vc-helpers>

// <vc-spec>
method Count(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>) 
  returns (result: seq<int>)
  requires |a| == |sub| == |start| == |endPos|
  requires forall i :: 0 <= i < |a| ==> start[i] <= endPos[i]
  requires forall i :: 0 <= i < |a| ==> 0 <= start[i] <= |a[i]|
  requires forall i :: 0 <= i < |a| ==> 0 <= endPos[i] <= |a[i]|
  requires forall i :: 0 <= i < |a| ==> |sub[i]| > 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] >= 0
  ensures forall i :: 0 <= i < |a| ==> 
    (|sub[i]| > endPos[i] - start[i] ==> result[i] == 0)
  ensures forall i :: 0 <= i < |a| ==>
    exists positions :: 
      |positions| == result[i] &&
      MaximalMatches(a[i], sub[i], positions, start[i], endPos[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build result via loop instead of seq comprehension and invoke GreedyMaximal per index */
  var n := |a|;
  var res: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == |GreedyPositions(a[j], sub[j], start[j], endPos[j])|
    invariant forall j :: 0 <= j < i ==> res[j] >= 0
    invariant forall j :: 0 <= j < i ==> (|sub[j]| > endPos[j] - start[j] ==> res[j] == 0)
    invariant forall j :: 0 <= j < i ==> MaximalMatches(a[j], sub[j], GreedyPositions(a[j], sub[j], start[j], endPos[j]), start[j], endPos[j])
    decreases n - i
  {
    GreedyMaximal(a[i], sub[i], start[i], endPos[i]);
    var gp := GreedyPositions(a[i], sub[i], start[i], endPos[i]);
    res := res + [|gp|];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
