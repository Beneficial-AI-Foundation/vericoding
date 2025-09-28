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
lemma StringGreaterIrrefl(s: string)
  ensures !StringGreater(s, s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    StringGreaterIrrefl(s[1..]);
  }
}

lemma StringGreaterAsym(s1: string, s2: string)
  ensures StringGreater(s1, s2) ==> !StringGreater(s2, s1)
  decreases |s1| + |s2|
{
  if StringGreater(s1, s2) {
    if |s2| == 0 {
      // |s2| == 0 => StringGreater(s2, s1) is false by definition
    } else if |s1| == 0 {
      // impossible under antecedent
    } else if s1[0] == s2[0] {
      StringGreaterAsym(s1[1..], s2[1..]);
    } else {
      // s1[0] > s2[0] implies s2[0] > s1[0] is false
    }
  }
}

lemma StringGreaterTrans(s1: string, s2: string, s3: string)
  ensures StringGreater(s1, s2) && StringGreater(s2, s3) ==> StringGreater(s1, s3)
  decreases |s1| + |s2| + |s3|
{
  if StringGreater(s1, s2) && StringGreater(s2, s3) {
    if |s3| == 0 {
      assert |s1| > 0;
      assert StringGreater(s1, s3);
    } else if |s1| == 0 || |s2| == 0 {
      // impossible under antecedent
    } else if s1[0] == s2[0] {
      if s2[0] == s3[0] {
        StringGreaterTrans(s1[1..], s2[1..], s3[1..]);
        assert s1[0] == s3[0];
        assert StringGreater(s1, s3);
      } else if s2[0] > s3[0] {
        assert s1[0] > s3[0];
        assert StringGreater(s1, s3);
      } else {
        // impossible under antecedent
      }
    } else if s1[0] > s2[0] {
      if s2[0] == s3[0] {
        assert s1[0] > s3[0];
        assert StringGreater(s1, s3);
      } else if s2[0] > s3[0] {
        assert s1[0] > s3[0];
        assert StringGreater(s1, s3);
      } else {
        // impossible under antecedent
      }
    } else {
      // impossible under antecedent
    }
  }
}

lemma StringGreaterTransForall(s1: string, s2: string)
  ensures StringGreater(s1, s2) ==> forall s :: StringGreater(s2, s) ==> StringGreater(s1, s)
  decreases |s1| + |s2|
{
  if StringGreater(s1, s2) {
    forall s | StringGreater(s2, s)
      ensures StringGreater(s1, s)
    {
      StringGreaterTrans(s1, s2, s);
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
  var r := new bool[|x1|];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant r.Length == |x1|
    invariant forall j :: 0 <= j < i ==> r[j] == StringGreater(x1[j], x2[j])
    invariant forall j :: 0 <= j < i ==> r[j] ==> !StringGreater(x2[j], x1[j])
    invariant forall j :: 0 <= j < i ==> x1[j] == x2[j] ==> !r[j]
    invariant forall j :: 0 <= j < i ==> r[j] ==> forall s :: StringGreater(x2[j], s) ==> StringGreater(x1[j], s)
  {
    r[i] := StringGreater(x1[i], x2[i]);
    if r[i] {
      StringGreaterAsym(x1[i], x2[i]);
      StringGreaterTransForall(x1[i], x2[i]);
    }
    if x1[i] == x2[i] {
      StringGreaterIrrefl(x1[i]);
    }
    i := i + 1;
  }
  result := r[..];
}
// </vc-code>
