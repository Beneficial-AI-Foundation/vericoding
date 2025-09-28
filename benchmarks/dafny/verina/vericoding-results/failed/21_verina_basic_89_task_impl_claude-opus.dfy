// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added proofs to lemmas and fixed contains function */
function contains(s: seq<int>, x: int): bool
{
  exists i :: 0 <= i < |s| && s[i] == x
}

function isUnique(s: seq<int>): bool
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma containsAppend(s: seq<int>, x: int)
  ensures contains(s + [x], x)
{
  assert (s + [x])[|s|] == x;
  assert 0 <= |s| < |s + [x]|;
}

lemma uniqueAppend(s: seq<int>, x: int)
  requires isUnique(s)
  requires !contains(s, x)
  ensures isUnique(s + [x])
{
  assert forall i, j :: 0 <= i < j < |s + [x]| ==>
    (j < |s| ==> (s + [x])[i] != (s + [x])[j]) &&
    (j == |s| ==> (s + [x])[j] == x && (s + [x])[i] != x);
}

lemma containsPreserved(s: seq<int>, x: int, y: int)
  requires contains(s, x)
  ensures contains(s + [y], x)
{
  var i :| 0 <= i < |s| && s[i] == x;
  assert (s + [y])[i] == x;
  assert 0 <= i < |s + [y]|;
}

lemma containsImpliesExists(s: seq<int>, x: int)
  requires contains(s, x)
  ensures exists j :: 0 <= j < |s| && s[j] == x
{
  // This follows directly from the definition of contains
}

lemma existsImpliesContains(s: seq<int>, x: int, j: int)
  requires 0 <= j < |s| && s[j] == x
  ensures contains(s, x)
{
  // This follows directly from the definition of contains
}
// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added assertions to help verify postconditions */
{
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant isUnique(result)
    invariant forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[k]
    invariant forall j :: 0 <= j < i ==> contains(result, s[j])
  {
    if !contains(result, s[i]) {
      uniqueAppend(result, s[i]);
      result := result + [s[i]];
      containsAppend(result[..|result|-1], s[i]);
    } else {
      var k :| 0 <= k < |result| && result[k] == s[i];
    }
    i := i + 1;
  }
  assert i == |s|;
  assert forall j :: 0 <= j < |s| ==> contains(result, s[j]);
  
  // Prove postcondition 1: uniqueness
  assert isUnique(result);
  assert forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j];
  
  // Prove postcondition 2: every element in result is in s
  assert forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[k];
  
  // Prove postcondition 3: every element in s is in result
  assert forall j :: 0 <= j < |s| ==> contains(result, s[j]);
  assert forall i: int :: 0 <= i < |s| ==> exists j: int :: 0 <= j < |result| && result[j] == s[i];
}
// </vc-code>
