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
/* helper modified by LLM (iteration 3): reflexivity of LexGreaterEqual */
lemma LexGreaterEqual_reflexive(s: string)
  ensures LexGreaterEqual(s, s)
  decreases |s|
{
  if |s| == 0 {
    // LexGreaterEqual("", "") holds by function definition
  } else {
    // s[0] == s[0], so recursive reasoning on tails
    LexGreaterEqual_reflexive(s[1..]);
  }
}

/* helper modified by LLM (iteration 3): antisymmetry of LexGreaterEqual */
lemma LexGreaterEqual_antisymmetric(s: string, t: string)
  ensures LexGreaterEqual(s, t) && LexGreaterEqual(t, s) ==> s == t
  decreases |s| + |t|
{
  if |s| == 0 {
    if LexGreaterEqual(s, t) && LexGreaterEqual(t, s) {
      // If s is empty and both relations hold, t must be empty as well
      assert |t| == 0;
      assert s == t;
    }
  } else if |t| == 0 {
    if LexGreaterEqual(s, t) && LexGreaterEqual(t, s) {
      // If t is empty and both relations hold, s must be empty as well
      assert |s| == 0;
      assert s == t;
    }
  } else {
    if LexGreaterEqual(s, t) && LexGreaterEqual(t, s) {
      if s[0] > t[0] {
        // Contradiction: if s[0] > t[0], then LexGreaterEqual(t,s) cannot hold
        assert false;
      } else if s[0] < t[0] {
        // Contradiction: if s[0] < t[0], then LexGreaterEqual(s,t) cannot hold
        assert false;
      } else {
        // s[0] == t[0], recurse on tails
        LexGreaterEqual_antisymmetric(s[1..], t[1..]);
        assert s[1..] == t[1..];
        assert s == t;
      }
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
{
  /* code modified by LLM (iteration 3): element-wise computation with helper lemma calls to assist verification */
  var n := |x1|;
  var a := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == LexGreaterEqual(x1[j], x2[j])
  {
    a[i] := LexGreaterEqual(x1[i], x2[i]);
    // Invoke helpers to assist verifier in reasoning about properties
    LexGreaterEqual_reflexive(x1[i]);
    LexGreaterEqual_reflexive(x2[i]);
    LexGreaterEqual_antisymmetric(x1[i], x2[i]);
    i := i + 1;
  }
  result := a[..];

  // Make postconditions explicit for the verifier
  assert |result| == |x1|;
  assert forall k :: 0 <= k < |result| ==> result[k] == LexGreaterEqual(x1[k], x2[k]);
  assert forall k :: 0 <= k < |x1| && x1[k] == x2[k] ==> result[k] == true;
  assert forall k :: 0 <= k < |x1| && LexGreaterEqual(x1[k], x2[k]) && LexGreaterEqual(x2[k], x1[k]) ==> x1[k] == x2[k];
}

// </vc-code>
