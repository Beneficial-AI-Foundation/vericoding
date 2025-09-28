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

lemma TransitiveHelper(a: string, b: string, c: string)
  requires StringGreater(a, b) && StringGreater(b, c)
  ensures StringGreater(a, c)
{
  if |a| == 0 || |b| == 0 || |c| == 0 {
    // Base case: if any string is empty, check StringGreater conditions
    // a > b requires a non-empty, b empty or a[0] > b[0]
    // b > c requires similar
    // If a is empty, StringGreater(a,b) is false, so we shouldn't be here
    // Similarly, if b is empty, StringGreater(b,c) requires |c|==0, but StringGreater(b,c)=true when b is empty only if c is empty
    // If c is empty, StringGreater(b,c)=true only if b is non-empty (since b empty implies false, non-empty b > empty c = true)
    if |a| == 0 {
      assert false; // a cannot be greater than b if a is empty
    } else if |b| == 0 {
      // b empty: StringGreater(b,c) true only if c empty
      if |c| != 0 { assert false; }
      // Then StringGreater(a,c): a non-empty > c empty = true
    } else if |c| == 0 {
      // StringGreater(b,c)=true (b non-empty > c empty)
      // StringGreater(a,c): a non-empty > c empty = true
    }
  } else if a[0] == b[0] && b[0] == c[0] {
    TransitiveHelper(a[1..], b[1..], c[1..]);
  } else if a[0] > b[0] {
    // If a[0] > b[0], then regardless of b and c, a[0] > c[0] or c prefix matches
    if b[0] == c[0] {
      // a[0] > c[0] since a[0] > b[0] == c[0]
    } else if b[0] > c[0] {
      // a[0] > b[0] > c[0] implies a[0] > c[0]
    } else {
      // b[0] < c[0], but StringGreater(b,c) requires b[0] > c[0] or prefix match
      // Since b[0] != c[0] and not (b[0] > c[0]), StringGreater(b,c) is false
      assert false;
    }
  } else if a[0] == b[0] {
    // Then b[0] > c[0] for StringGreater(b,c) to hold
    if b[0] > c[0] {
      // a[0] == b[0] > c[0] so a[0] > c[0]
    } else {
      assert false; // StringGreater(b,c) requires b[0] > c[0] or prefix match
    }
  } else {
    assert false; // a[0] < b[0], but StringGreater(a,b) requires a[0] > b[0] or prefix match
  }
}

lemma AsymmetryHelper(s1: string, s2: string)
  ensures StringGreater(s1, s2) ==> !StringGreater(s2, s1)
{
  if StringGreater(s1, s2) {
    if |s1| == 0 {
      assert false; // Empty s1 cannot be greater than s2
    } else if |s2| == 0 {
      // s2 empty: StringGreater(s2,s1) = false since |s1| != 0
    } else if s1[0] > s2[0] {
      // s2[0] cannot be > s1[0] since s1[0] > s2[0]
    } else if s1[0] == s2[0] {
      AsymmetryHelper(s1[1..], s2[1..]);
    }
  }
}

lemma IrreflexivityHelper(s: string)
  ensures !StringGreater(s, s)
{
  if |s| == 0 {
    // Empty string: StringGreater(s, s) = false
  } else {
    // StringGreater(s,s): if |s|!=0, check s[0] == s[0] then recursive call
    // Since s[0] == s[0], it calls StringGreater(s[1..], s[1..])
    // By induction, StringGreater(s[1..], s[1..]) is false
    IrreflexivityHelper(s[1..]);
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
  /* code modified by LLM (iteration 2): fixed index out of range and verification */
  result := seq(|x1|, i requires 0 <= i < |x1| => StringGreater(x1[i], x2[i]));
  
  // Verify asymmetry
  forall i | 0 <= i < |result| && result[i]
    ensures !StringGreater(x2[i], x1[i])
  {
    AsymmetryHelper(x1[i], x2[i]);
  }
  
  // Verify irreflexivity for equal strings
  forall i | 0 <= i < |result| && x1[i] == x2[i]
    ensures !result[i]
  {
    IrreflexivityHelper(x1[i]);
  }
  
  // Verify transitivity
  forall i | 0 <= i < |result| && result[i]
    ensures forall s :: StringGreater(x2[i], s) ==> StringGreater(x1[i], s)
  {
    forall s | StringGreater(x2[i], s)
      ensures StringGreater(x1[i], s)
    {
      TransitiveHelper(x1[i], x2[i], s);
    }
  }
}
// </vc-code>
