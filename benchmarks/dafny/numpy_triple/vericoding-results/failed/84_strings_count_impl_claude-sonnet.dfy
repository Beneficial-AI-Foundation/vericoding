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
/* helper modified by LLM (iteration 5): Fixed sequence comprehension syntax errors */
function FindMaxMatches(s: string, sub: string, start: int, endPos: int): int
  requires 0 <= start <= endPos <= |s|
  requires |sub| > 0
  ensures FindMaxMatches(s, sub, start, endPos) >= 0
  ensures |sub| > endPos - start ==> FindMaxMatches(s, sub, start, endPos) == 0
  decreases endPos - start
{
  if |sub| > endPos - start then 0
  else if start >= endPos then 0
  else
    var found := if SubstringAt(s, sub, start) then 1 + FindMaxMatches(s, sub, start + |sub|, endPos)
                 else 0;
    var skip := FindMaxMatches(s, sub, start + 1, endPos);
    if found >= skip then found else skip
}

/* helper modified by LLM (iteration 5): Fixed postconditions to ensure proper verification */
function ConstructPositions(s: string, sub: string, start: int, endPos: int): seq<int>
  requires 0 <= start <= endPos <= |s|
  requires |sub| > 0
  ensures |ConstructPositions(s, sub, start, endPos)| == FindMaxMatches(s, sub, start, endPos)
  ensures ValidMatches(s, sub, ConstructPositions(s, sub, start, endPos), start, endPos)
  ensures NonOverlapping(ConstructPositions(s, sub, start, endPos), |sub|)
  decreases endPos - start
{
  if |sub| > endPos - start then []
  else if start >= endPos then []
  else
    var found := if SubstringAt(s, sub, start) then 1 + FindMaxMatches(s, sub, start + |sub|, endPos)
                 else 0;
    var skip := FindMaxMatches(s, sub, start + 1, endPos);
    if found >= skip then
      if SubstringAt(s, sub, start) then 
        var rest := ConstructPositions(s, sub, start + |sub|, endPos);
        [start] + rest
      else ConstructPositions(s, sub, start + 1, endPos)
    else ConstructPositions(s, sub, start + 1, endPos)
}

/* helper modified by LLM (iteration 5): Lemma to prove maximality property */
lemma ProveMaximality(s: string, sub: string, positions: seq<int>, start: int, endPos: int)
  requires 0 <= start <= endPos <= |s|
  requires |sub| > 0
  requires positions == ConstructPositions(s, sub, start, endPos)
  ensures MaximalMatches(s, sub, positions, start, endPos)
{
  assert ValidMatches(s, sub, positions, start, endPos);
  assert NonOverlapping(positions, |sub|);
  
  forall otherPositions | 
    |otherPositions| <= (endPos - start) &&
    (forall pos :: pos in otherPositions ==> start <= pos && pos + |sub| <= endPos) &&
    ValidMatches(s, sub, otherPositions, start, endPos) && 
    NonOverlapping(otherPositions, |sub|)
  ensures |otherPositions| <= |positions|
  {
    MaximalityHelper(s, sub, positions, otherPositions, start, endPos);
  }
}

/* helper modified by LLM (iteration 5): Helper lemma for maximality proof with fixed sequence comprehension */
lemma MaximalityHelper(s: string, sub: string, positions: seq<int>, otherPositions: seq<int>, start: int, endPos: int)
  requires 0 <= start <= endPos <= |s|
  requires |sub| > 0
  requires positions == ConstructPositions(s, sub, start, endPos)
  requires |otherPositions| <= (endPos - start)
  requires forall pos :: pos in otherPositions ==> start <= pos && pos + |sub| <= endPos
  requires ValidMatches(s, sub, otherPositions, start, endPos)
  requires NonOverlapping(otherPositions, |sub|)
  ensures |otherPositions| <= |positions|
  decreases endPos - start
{
  if |sub| > endPos - start || start >= endPos {
    assert |positions| == 0;
  } else {
    var found := if SubstringAt(s, sub, start) then 1 + FindMaxMatches(s, sub, start + |sub|, endPos) else 0;
    var skip := FindMaxMatches(s, sub, start + 1, endPos);
    
    if found >= skip {
      if SubstringAt(s, sub, start) {
        var otherAfter := seq(|otherPositions|, i requires 0 <= i < |otherPositions| => 
          if otherPositions[i] >= start + |sub| then otherPositions[i] else -1);
        var filteredAfter := seq(i <- 0..|otherAfter| | otherAfter[i] >= 0, otherAfter[i]);
        MaximalityHelper(s, sub, ConstructPositions(s, sub, start + |sub|, endPos), filteredAfter, start + |sub|, endPos);
      } else {
        var otherAfter := seq(|otherPositions|, i requires 0 <= i < |otherPositions| => 
          if otherPositions[i] >= start + 1 then otherPositions[i] else -1);
        var filteredAfter := seq(i <- 0..|otherAfter| | otherAfter[i] >= 0, otherAfter[i]);
        MaximalityHelper(s, sub, ConstructPositions(s, sub, start + 1, endPos), filteredAfter, start + 1, endPos);
      }
    } else {
      var otherAfter := seq(|otherPositions|, i requires 0 <= i < |otherPositions| => 
        if otherPositions[i] >= start + 1 then otherPositions[i] else -1);
      var filteredAfter := seq(i <- 0..|otherAfter| | otherAfter[i] >= 0, otherAfter[i]);
      MaximalityHelper(s, sub, ConstructPositions(s, sub, start + 1, endPos), filteredAfter, start + 1, endPos);
    }
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
  /* code modified by LLM (iteration 5): Added explicit maximality proof */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] >= 0
    invariant forall j :: 0 <= j < i ==> (|sub[j]| > endPos[j] - start[j] ==> result[j] == 0)
    invariant forall j :: 0 <= j < i ==> 
      var positions := ConstructPositions(a[j], sub[j], start[j], endPos[j]);
      |positions| == result[j] && MaximalMatches(a[j], sub[j], positions, start[j], endPos[j])
  {
    var count := FindMaxMatches(a[i], sub[i], start[i], endPos[i]);
    var positions := ConstructPositions(a[i], sub[i], start[i], endPos[i]);
    ProveMaximality(a[i], sub[i], positions, start[i], endPos[i]);
    assert |positions| == count;
    assert MaximalMatches(a[i], sub[i], positions, start[i], endPos[i]);
    result := result + [count];
    i := i + 1;
  }
}
// </vc-code>
