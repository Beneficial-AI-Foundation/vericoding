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
/* helper modified by LLM (iteration 3): Added lemmas to prove asymmetry and transitivity properties */
lemma StringGreaterAsymmetry(s1: string, s2: string)
    ensures StringGreater(s1, s2) ==> !StringGreater(s2, s1)
{
    if |s1| == 0 {
        // s1 is empty, so StringGreater(s1, s2) is false
        assert !StringGreater(s1, s2);
    } else if |s2| == 0 {
        // s2 is empty and s1 is not, so StringGreater(s1, s2) is true
        // and StringGreater(s2, s1) is false
        assert StringGreater(s1, s2);
        assert !StringGreater(s2, s1);
    } else if s1[0] == s2[0] {
        StringGreaterAsymmetry(s1[1..], s2[1..]);
    } else {
        // s1[0] != s2[0], so exactly one of s1[0] > s2[0] or s2[0] > s1[0] is true
        assert s1[0] > s2[0] ==> !(s2[0] > s1[0]);
    }
}

lemma StringGreaterTransitivity(s1: string, s2: string, s3: string)
    ensures StringGreater(s1, s2) && StringGreater(s2, s3) ==> StringGreater(s1, s3)
{
    if StringGreater(s1, s2) && StringGreater(s2, s3) {
        StringGreaterTransitivityHelper(s1, s2, s3);
    }
}

lemma StringGreaterTransitivityHelper(s1: string, s2: string, s3: string)
    requires StringGreater(s1, s2)
    requires StringGreater(s2, s3)
    ensures StringGreater(s1, s3)
    decreases |s1| + |s2| + |s3|
{
    if |s2| == 0 {
        // StringGreater(s2, s3) would be false, contradiction
        assert false;
    } else if |s3| == 0 {
        // StringGreater(s2, s3) is true, and |s3| == 0
        // We need to show StringGreater(s1, s3) which is true when |s3| == 0 and |s1| > 0
        if |s1| == 0 {
            // StringGreater(s1, s2) would be false, contradiction
            assert false;
        }
    } else if |s1| == 0 {
        // StringGreater(s1, s2) would be false, contradiction
        assert false;
    } else {
        // All strings are non-empty
        if s1[0] > s3[0] {
            // Direct comparison gives us the result
        } else if s1[0] == s3[0] {
            // Need to recurse on tails
            if s1[0] == s2[0] && s2[0] == s3[0] {
                StringGreaterTransitivityHelper(s1[1..], s2[1..], s3[1..]);
            } else if s1[0] == s2[0] {
                // s2[0] > s3[0], so StringGreater(s1[1..], s2[1..]) and s2[0] > s3[0]
                assert StringGreater(s1, s3);
            } else if s2[0] == s3[0] {
                // s1[0] > s2[0], so s1[0] > s3[0]
                assert StringGreater(s1, s3);
            } else {
                // s1[0] > s2[0] > s3[0], so s1[0] > s3[0]
                assert StringGreater(s1, s3);
            }
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
  /* code modified by LLM (iteration 3): Added explicit proof of transitivity in loop body */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == StringGreater(x1[j], x2[j])
    invariant forall j :: 0 <= j < i ==> result[j] ==> !StringGreater(x2[j], x1[j])
    invariant forall j :: 0 <= j < i ==> result[j] ==> forall s :: StringGreater(x2[j], s) ==> StringGreater(x1[j], s)
  {
    var comp := StringGreater(x1[i], x2[i]);
    StringGreaterAsymmetry(x1[i], x2[i]);
    
    // Prove transitivity for the current element
    forall s | StringGreater(x2[i], s)
      ensures comp ==> StringGreater(x1[i], s)
    {
      if comp {
        StringGreaterTransitivity(x1[i], x2[i], s);
      }
    }
    
    result := result + [comp];
    i := i + 1;
  }
}
// </vc-code>
