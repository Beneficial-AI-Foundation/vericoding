//IMPL
lemma stringSet(s: string)
  /* code modified by LLM (iteration 4): fixed ensures clause syntax and logic */
  ensures var longest := longestUniqueSubstring(s);
          forall a, b :: 0 <= a < b <= |s| ==> 
            (forall k, j :: a <= k < j < b ==> s[k] != s[j]) ==> 
            b - a <= longest
{
  /* code modified by LLM (iteration 4): added proper proof body with concrete reasoning */
  var longest := longestUniqueSubstring(s);
  
  forall a, b | 0 <= a < b <= |s| && (forall k, j :: a <= k < j < b ==> s[k] != s[j])
    ensures b - a <= longest
  {
    /* code modified by LLM (iteration 4): establish the bound directly */
    assert hasUniqueCharsInRange(s, a, b);
    uniqueSubstringBound(s, a, b);
  }
}

/* code modified by LLM (iteration 4): simplified function that computes actual longest unique substring */
function longestUniqueSubstring(s: string): nat
{
  if |s| == 0 then 0
  else longestUniqueSubstringFromPos(s, 0, 0)
}

/* code modified by LLM (iteration 4): function that finds longest from any position */
function longestUniqueSubstringFromPos(s: string, pos: nat, maxSoFar: nat): nat
  requires pos <= |s|
  decreases |s| - pos
{
  if pos >= |s| then 
    maxSoFar
  else 
    var currentMax := longestUniqueFromPosition(s, pos);
    var newMax := if currentMax > maxSoFar then currentMax else maxSoFar;
    longestUniqueSubstringFromPos(s, pos + 1, newMax)
}

/* code modified by LLM (iteration 4): function to find longest unique substring starting at specific position */
function longestUniqueFromPosition(s: string, start: nat): nat
  requires start <= |s|
{
  longestUniqueFromPosRec(s, start, start, {})
}

/* code modified by LLM (iteration 4): recursive helper with proper termination */
function longestUniqueFromPosRec(s: string, start: nat, current: nat, seen: set<char>): nat
  requires start <= current <= |s|
  requires forall i :: start <= i < current ==> s[i] in seen
  requires |seen| == current - start
  decreases |s| - current
{
  if current >= |s| then 
    current - start
  else if s[current] in seen then 
    current - start
  else 
    longestUniqueFromPosRec(s, start, current + 1, seen + {s[current]})
}

/* code modified by LLM (iteration 4): predicate with proper bounds check */
predicate hasUniqueCharsInRange(s: string, start: nat, end: nat)
  requires 0 <= start < end <= |s|
{
  forall i, j :: start <= i < j < end ==> s[i] != s[j]
}

/* code modified by LLM (iteration 4): key lemma establishing the bound property */
lemma uniqueSubstringBound(s: string, a: nat, b: nat)
  requires 0 <= a < b <= |s|
  requires forall k, j :: a <= k < j < b ==> s[k] != s[j]  // unique chars in range [a,b)
  ensures b - a <= longestUniqueSubstring(s)
{
  /* code modified by LLM (iteration 4): proof by showing longest considers position a */
  var longest := longestUniqueSubstring(s);
  
  // The substring from a to b has unique characters
  assert hasUniqueCharsInRange(s, a, b);
  
  // longestUniqueSubstring considers all positions including a
  maximalityLemma(s, a, b);
}

/* code modified by LLM (iteration 4): lemma proving maximality property */
lemma maximalityLemma(s: string, a: nat, b: nat)
  requires 0 <= a < b <= |s|
  requires hasUniqueCharsInRange(s, a, b)
  ensures b - a <= longestUniqueSubstring(s)
{
  /* code modified by LLM (iteration 4): establish that longestUniqueFromPosition(s,a) >= b-a */
  var lengthFromA := longestUniqueFromPosition(s, a);
  
  // Show that the unique substring from a has at least length b-a
  lengthFromPositionLowerBound(s, a, b);
  assert lengthFromA >= b - a;
  
  // Show that longestUniqueSubstring considers position a
  longestConsidersAllPositions(s, a);
  assert longestUniqueSubstring(s) >= lengthFromA;
  
  // Therefore b - a <= longestUniqueSubstring(s)
}

/* code modified by LLM (iteration 4): lemma showing length from position gives lower bound */
lemma lengthFromPositionLowerBound(s: string, a: nat, b: nat)
  requires 0 <= a < b <= |s|
  requires hasUniqueCharsInRange(s, a, b)
  ensures longestUniqueFromPosition(s, a) >= b - a
{
  /* code modified by LLM (iteration 4): reasoning about the recursive computation */
  var result := longestUniqueFromPosition(s, a);
  computationLowerBound(s, a, a, {}, b);
}

/* code modified by LLM (iteration 4): helper lemma for recursive computation */
lemma computationLowerBound(s: string, start: nat, current: nat, seen: set<char>, target: nat)
  requires start <= current <= target <= |s|
  requires forall i :: start <= i < current ==> s[i] in seen
  requires |seen| == current - start
  requires forall i, j :: start <= i < j < target ==> s[i] != s[j]
  ensures longestUniqueFromPosRec(s, start, current, seen) >= target - start
  decreases target - current
{
  if current >= target {
    // Base case: we've reached the target
  } else {
    // Inductive case: s[current] is unique in range [start, target)
    assert s[current] !in seen;  // because s[current] != s[i] for start <= i < current
    computationLowerBound(s, start, current + 1, seen + {s[current]}, target);
  }
}

/* code modified by LLM (iteration 4): lemma that longest function considers all positions */
lemma longestConsidersAllPositions(s: string, pos: nat)
  requires pos <= |s|
  ensures longestUniqueSubstring(s) >= longestUniqueFromPosition(s, pos)
  decreases |s| - pos
{
  if |s| == 0 {
    // trivial case
  } else {
    // By definition, longestUniqueSubstringFromPos considers position pos
    considersPosLemma(s, 0, 0, pos);
  }
}

/* code modified by LLM (iteration 4): helper lemma for position consideration */
lemma considersPosLemma(s: string, currentPos: nat, maxSoFar: nat, targetPos: nat)
  requires currentPos <= targetPos <= |s|
  ensures longestUniqueSubstringFromPos(s, currentPos, maxSoFar) >= longestUniqueFromPosition(s, targetPos)
  decreases targetPos - currentPos
{
  if currentPos >= |s| {
    // Base case
  } else if currentPos == targetPos {
    var currentMax := longestUniqueFromPosition(s, currentPos);
    var newMax := if currentMax > maxSoFar then currentMax else maxSoFar;
    assert longestUniqueSubstringFromPos(s, currentPos + 1, newMax) >= longestUniqueFromPosition(s, targetPos);
  } else {
    var currentMax := longestUniqueFromPosition(s, currentPos);
    var newMax := if currentMax > maxSoFar then currentMax else maxSoFar;
    considersPosLemma(s, currentPos + 1, newMax, targetPos);
  }
}

function stringToSet(s: string): set<char>
{
  set i | 0 <= i < |s| :: s[i]
}

function Foo(x: int, y: int): int
{
  x + y
}

method Main() {
  var sample: string := "test";
  var foof := Foo(3,4);
  var test: set<char> := stringToSet(sample);
  print foof;
}