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
/* helper modified by LLM (iteration 5): CompareCounts - shows |other| <= |positions| by building a mapping and recursing */
lemma CompareCounts(positions: seq<int>, other: seq<int>, subLen: int)
  requires subLen > 0
  requires NonOverlapping(positions, subLen)
  requires NonOverlapping(other, subLen)
  requires forall y :: y in other ==> exists j :: 0 <= j < |positions| && positions[j] <= y < positions[j] + subLen
  ensures |other| <= |positions|
  decreases |other|
{
  if |other| == 0 {
    return;
  }
  var y := other[0];
  // find an index j in positions that covers y (existence guaranteed by requires)
  var j := 0;
  while !(0 <= j < |positions| && positions[j] <= y < positions[j] + subLen)
    invariant 0 <= j <= |positions|
    decreases |positions| - j
  {
    j := j + 1;
  }
  assert 0 <= j < |positions|;

  var otherTail := other[1..];
  var positionsTail := positions[..j] + positions[j+1..];
  assert NonOverlapping(positionsTail, subLen);

  // For each z in otherTail, show it is covered by some element of positionsTail.
  // We find jprime in positions, then map it to positionsTail index.
  forall z | z in otherTail {
    var jprime := 0;
    while !(0 <= jprime < |positions| && positions[jprime] <= z < positions[jprime] + subLen)
      invariant 0 <= jprime <= |positions|
      decreases |positions| - jprime
    {
      jprime := jprime + 1;
    }
    assert 0 <= jprime < |positions|;
    if jprime < j {
      var k := jprime;
      assert 0 <= k < |positionsTail|;
      assert positionsTail[k] == positions[k];
      assert positionsTail[k] <= z < positionsTail[k] + subLen;
    } else if jprime > j {
      var k := jprime - 1;
      assert 0 <= k < |positionsTail|;
      assert positionsTail[k] == positions[jprime];
      assert positionsTail[k] <= z < positionsTail[k] + subLen;
    } else {
      // jprime == j leads to contradiction because other is NonOverlapping and z >= y + subLen
      // derive contradiction: positions[j] <= y < positions[j] + subLen and positions[j] <= z < positions[j] + subLen
      assert positions[j] <= y < positions[j] + subLen;
      assert positions[j] <= z < positions[j] + subLen;
      // other is NonOverlapping, so z >= y + subLen
      assert z >= y + subLen;
      // therefore positions[j] + subLen <= z, contradicting z < positions[j] + subLen
      assert positions[j] + subLen <= z;
      assert false;
    }
  }

  // Recurse on tails
  CompareCounts(positionsTail, otherTail, subLen);
  assert |otherTail| <= |positionsTail|;
  assert |other| == 1 + |otherTail|;
  assert |positions| == 1 + |positionsTail|;
  assert |other| <= |positions|;
}

/* helper modified by LLM (iteration 5): GreedyMaximalLemma - uses CompareCounts to show maximality of greedy matches */
lemma GreedyMaximalLemma(s: string, sub: string, start: int, endPos: int, positions: seq<int>)
  requires |sub| > 0
  requires ValidMatches(s, sub, positions, start, endPos)
  requires NonOverlapping(positions, |sub|)
  requires forall x :: start <= x && x + |sub| <= endPos && SubstringAt(s, sub, x) ==> exists j :: 0 <= j < |positions| && positions[j] <= x < positions[j] + |sub|
  ensures MaximalMatches(s, sub, positions, start, endPos)
{
  forall otherPositions |
    |otherPositions| <= (endPos - start) &&
    (forall pos :: pos in otherPositions ==> start <= pos && pos + |sub| <= endPos) &&
    (ValidMatches(s, sub, otherPositions, start, endPos) && NonOverlapping(otherPositions, |sub|))
  {
    var other := otherPositions;
    if |other| == 0 {
      assert |other| <= |positions|;
    } else {
      // from the last requires we have for each y in other an index in positions that covers y
      assert forall y :: y in other ==> exists j :: 0 <= j < |positions| && positions[j] <= y < positions[j] + |sub|;
      CompareCounts(positions, other, |sub|);
    }
  }
}

/* helper modified by LLM (iteration 5): GreedyMatches - construct greedy non-overlapping matches and prove maximality */
method GreedyMatches(s: string, sub: string, start: int, endPos: int) returns (count: int, positions: seq<int>)
  requires 0 <= start <= |s|
  requires 0 <= endPos <= |s|
  requires start <= endPos
  requires |sub| > 0
  ensures |positions| == count
  ensures ValidMatches(s, sub, positions, start, endPos)
  ensures NonOverlapping(positions, |sub|)
  ensures MaximalMatches(s, sub, positions, start, endPos)
{
  var pos := start;
  positions := [];
  while pos + |sub| <= endPos
    invariant start <= pos <= endPos
    invariant ValidMatches(s, sub, positions, start, endPos)
    invariant NonOverlapping(positions, |sub|)
    invariant forall x :: start <= x < pos && SubstringAt(s, sub, x) ==> exists j :: 0 <= j < |positions| && positions[j] <= x < positions[j] + |sub|
  {
    if SubstringAt(s, sub, pos) {
      positions := positions + [pos];
      pos := pos + |sub|;
    } else {
      pos := pos + 1;
    }
  }
  count := |positions|;
  assert forall x :: start <= x && x + |sub| <= endPos && SubstringAt(s, sub, x) ==> exists j :: 0 <= j < |positions| && positions[j] <= x < positions[j] + |sub|;
  GreedyMaximalLemma(s, sub, start, endPos, positions);
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
  /* code modified by LLM (iteration 5): iterate over inputs, call GreedyMatches, and build result while preserving witnesses */
  var i := 0;
  var res: seq<int> := [];
  var posSeqs: seq<seq<int>> := [];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant |posSeqs| == i
    invariant forall k :: 0 <= k < i ==> |posSeqs[k]| == res[k] && MaximalMatches(a[k], sub[k], posSeqs[k], start[k], endPos[k])
  {
    var cnt: int;
    var posseq: seq<int>;
    cnt, posseq := GreedyMatches(a[i], sub[i], start[i], endPos[i]);
    res := res + [cnt];
    posSeqs := posSeqs + [posseq];
    i := i + 1;
  }
  result := res;
}

// </vc-code>
