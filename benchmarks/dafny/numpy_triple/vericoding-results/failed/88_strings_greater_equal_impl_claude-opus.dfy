// <vc-preamble>
/*
 * Dafny specification for numpy.strings.greater_equal
 * 
 * Performs element-wise lexicographic string comparison, returning a boolean sequence
 * indicating whether each string in x1 is greater than or equal to the corresponding 
 * string in x2.
 */

// Helper function for lexicographic string comparison
function LexGreaterEqual(s1: string, s2: string): bool
{
  if |s1| == 0 then true
  else if |s2| == 0 then true
  else if s1[0] > s2[0] then true
  else if s1[0] < s2[0] then false
  else LexGreaterEqual(s1[1..], s2[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemmas for original LexGreaterEqual function */
lemma LexGreaterEqualReflexive(s: string)
  ensures LexGreaterEqual(s, s)
{
  if |s| > 0 {
    LexGreaterEqualReflexive(s[1..]);
  }
}

lemma LexGreaterEqualAntisymmetric(s1: string, s2: string)
  requires LexGreaterEqual(s1, s2)
  requires LexGreaterEqual(s2, s1)
  ensures s1 == s2
{
  if |s1| == 0 && |s2| == 0 {
    // Both empty, trivially equal
  } else if |s1| == 0 {
    // s1 empty but LexGreaterEqual(s1, s2) is true, so s2 must be empty
    assert |s2| == 0;
  } else if |s2| == 0 {
    // s2 empty but LexGreaterEqual(s2, s1) is true, so s1 must be empty
    assert |s1| == 0;
  } else {
    // Both non-empty
    if s1[0] > s2[0] {
      // LexGreaterEqual(s2, s1) would be false
      assert false;
    } else if s1[0] < s2[0] {
      // LexGreaterEqual(s1, s2) would be false
      assert false;
    } else {
      // s1[0] == s2[0], recurse on tails
      assert s1[0] == s2[0];
      LexGreaterEqualAntisymmetric(s1[1..], s2[1..]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method GreaterEqual(x1: seq<string>, x2: seq<string>) returns (result: seq<bool>)
  // Precondition: input sequences must have the same length
  requires |x1| == |x2|
  
  // Postcondition: result has same length as inputs
  ensures |result| == |x1|
  
  // Core property: element-wise lexicographic comparison
  ensures forall i :: 0 <= i < |result| ==> result[i] == LexGreaterEqual(x1[i], x2[i])
  
  // Reflexive property: every string is >= itself
  ensures forall i :: 0 <= i < |x1| && x1[i] == x2[i] ==> result[i] == true
  
  // Antisymmetric property: if s1 >= s2 and s2 >= s1, then s1 == s2
  ensures forall i :: 0 <= i < |x1| && LexGreaterEqual(x1[i], x2[i]) && LexGreaterEqual(x2[i], x1[i]) ==> x1[i] == x2[i]
  
  // Empty string properties: empty string is <= any string, any string is >= empty string
  ensures forall i :: 0 <= i < |x1| && x1[i] == "" && x2[i] == "" ==> result[i] == true
  ensures forall i :: 0 <= i < |x1| && x1[i] != "" && x2[i] == "" ==> result[i] == true
  
  // Deterministic property: function behavior is deterministic
  ensures forall y1: seq<string>, y2: seq<string> :: |y1| == |x1| && |y2| == |x2| && y1 == x1 && y2 == x2 ==>
    exists r: seq<bool> :: |r| == |result| && (forall j :: 0 <= j < |r| ==> r[j] == LexGreaterEqual(y1[j], y2[j]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed lemma calls to use correct names */
{
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == LexGreaterEqual(x1[j], x2[j])
    invariant forall j :: 0 <= j < i && x1[j] == x2[j] ==> result[j] == true
    invariant forall j :: 0 <= j < i && LexGreaterEqual(x1[j], x2[j]) && LexGreaterEqual(x2[j], x1[j]) ==> x1[j] == x2[j]
  {
    if x1[i] == x2[i] {
      LexGreaterEqualReflexive(x1[i]);
    }
    if LexGreaterEqual(x1[i], x2[i]) && LexGreaterEqual(x2[i], x1[i]) {
      LexGreaterEqualAntisymmetric(x1[i], x2[i]);
    }
    result := result + [LexGreaterEqual(x1[i], x2[i])];
    i := i + 1;
  }
}
// </vc-code>
