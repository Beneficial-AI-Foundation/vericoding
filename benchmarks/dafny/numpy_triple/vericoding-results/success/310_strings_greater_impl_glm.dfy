// <vc-preamble>
predicate StringGreater(s1: string, s2: string)
{
    if |s1| == 0 then false
    else if |s2| == 0 then true
    else if s1[0] == s2[0] then StringGreater(s1[1..], s2[1..])
    else s1[0] > s2[0]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemmas for StringGreater properties */
lemma StringGreaterAsymmetry(s1: string, s2: string)
  requires StringGreater(s1, s2)
  ensures !StringGreater(s2, s1)
  decreases |s1| + |s2|
{
  if |s1| == 0 {
  } else if |s2| == 0 {
  } else {
    if s1[0] == s2[0] {
      StringGreaterAsymmetry(s1[1..], s2[1..]);
    }
  }
}

lemma StringGreaterTransitivity(s1: string, s2: string, s3: string)
  requires StringGreater(s1, s2)
  requires StringGreater(s2, s3)
  ensures StringGreater(s1, s3)
  decreases |s1| + |s2| + |s3|
{
  if |s1| == 0 {
  } else if |s2| == 0 {
  } else if |s3| == 0 {
  } else {
    if s1[0] == s2[0] && s2[0] == s3[0] {
      StringGreaterTransitivity(s1[1..], s2[1..], s3[1..]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Greater(x1: seq<string>, x2: seq<string>) returns (result: seq<bool>)
    // Input vectors must have the same length
    requires |x1| == |x2|
    
    // Output vector has same length as input vectors
    ensures |result| == |x1|
    
    // Core property: result[i] = (x1[i] > x2[i]) for all indices
    ensures forall i :: 0 <= i < |result| ==> result[i] == StringGreater(x1[i], x2[i])
    
    // Asymmetry: if x1[i] > x2[i], then NOT (x2[i] > x1[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] ==> !StringGreater(x2[i], x1[i])
    
    // Irreflexivity: no string is greater than itself
    ensures forall i :: 0 <= i < |result| ==> x1[i] == x2[i] ==> !result[i]
    
    // Transitivity property: if x1[i] > x2[i] and s < x2[i], then x1[i] > s
    ensures forall i :: 0 <= i < |result| ==> result[i] ==> 
            forall s :: StringGreater(x2[i], s) ==> StringGreater(x1[i], s)
    
    // Decidability: result is always boolean (true or false)
    ensures forall i :: 0 <= i < |result| ==> result[i] || !result[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added postcondition proofs using lemmas */
  var n := |x1|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == StringGreater(x1[j], x2[j])
  {
    result := result + [StringGreater(x1[i], x2[i])];
    i := i + 1;
  }

  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> result[j] ==> !StringGreater(x2[j], x1[j])
    invariant forall j :: 0 <= j < i ==> result[j] ==> 
            forall s :: StringGreater(x2[j], s) ==> StringGreater(x1[j], s)
  {
    if result[i] {
      StringGreaterAsymmetry(x1[i], x2[i]);
      forall s | StringGreater(x2[i], s)
        ensures StringGreater(x1[i], s)
      {
        StringGreaterTransitivity(x1[i], x2[i], s);
      }
    }
    i := i + 1;
  }
}
// </vc-code>
