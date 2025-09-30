// <vc-preamble>
// Helper function to compute sum of array elements recursively
function Sum(s: seq<real>): real
{
    if |s| == 0 then 0.0
    else s[0] + Sum(s[1..])
}

// Predicate to check if all elements in sequence are zero
predicate AllZero(s: seq<real>)
{
    forall i :: 0 <= i < |s| ==> s[i] == 0.0
}

/**
 * Sum of array elements - computes the sum of all elements in the vector.
 * For empty vectors, returns 0 as the identity element of addition.
 * This is a reduction operation that applies addition across all elements.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed SumPrefix lemma to handle all cases correctly */
lemma SumPrefix(s: seq<real>, i: int)
  requires 0 <= i <= |s|
  ensures Sum(s[..i]) + Sum(s[i..]) == Sum(s)
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
    assert Sum([]) == 0.0;
    assert Sum(s[..i]) + Sum(s[i..]) == 0.0 + Sum(s) == Sum(s);
  } else if i == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
    assert Sum([]) == 0.0;
    assert Sum(s[..i]) + Sum(s[i..]) == Sum(s) + 0.0 == Sum(s);
  } else if |s| == 0 {
    assert false; // This case is impossible given 0 <= i <= |s| and i != 0 and i != |s|
  } else {
    // Case: 0 < i < |s|, so |s| > 0
    assert s == [s[0]] + s[1..];
    assert Sum(s) == s[0] + Sum(s[1..]);
    
    if i == 1 {
      assert s[..1] == [s[0]];
      assert Sum(s[..1]) == s[0];
      assert s[1..] == s[1..];
      assert Sum(s[..1]) + Sum(s[1..]) == s[0] + Sum(s[1..]) == Sum(s);
    } else {
      // i > 1
      assert s[..i] == [s[0]] + s[1..][..i-1];
      assert Sum(s[..i]) == s[0] + Sum(s[1..][..i-1]);
      assert s[i..] == s[1..][i-1..];
      SumPrefix(s[1..], i-1);
      assert Sum(s[1..][..i-1]) + Sum(s[1..][i-1..]) == Sum(s[1..]);
      assert Sum(s[..i]) + Sum(s[i..]) == (s[0] + Sum(s[1..][..i-1])) + Sum(s[1..][i-1..]);
      assert Sum(s[..i]) + Sum(s[i..]) == s[0] + (Sum(s[1..][..i-1]) + Sum(s[1..][i-1..]));
      assert Sum(s[..i]) + Sum(s[i..]) == s[0] + Sum(s[1..]);
      assert Sum(s[..i]) + Sum(s[i..]) == Sum(s);
    }
  }
}

lemma AllZeroImpliesSumZero(s: seq<real>)
  requires AllZero(s)
  ensures Sum(s) == 0.0
{
  if |s| == 0 {
    assert Sum(s) == 0.0;
  } else {
    assert s[0] == 0.0;
    assert AllZero(s[1..]);
    AllZeroImpliesSumZero(s[1..]);
    assert Sum(s) == s[0] + Sum(s[1..]) == 0.0 + 0.0 == 0.0;
  }
}
// </vc-helpers>

// <vc-spec>
method sum(a: array<real>) returns (result: real)
    requires true
    ensures result == Sum(a[..])  // Result equals sum of all elements using recursive definition
    ensures a.Length == 0 ==> result == 0.0  // Empty array returns 0 (additive identity)
    ensures AllZero(a[..]) ==> result == 0.0  // If all elements are zero, result is zero
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Added proper loop invariants and lemma calls to verify sum computation */
{
  var i := 0;
  result := 0.0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == Sum(a[..i])
    invariant a[..i] == a[..][..i]
  {
    // Before updating result, establish that Sum(a[..i+1]) == Sum(a[..i]) + a[i]
    assert a[..i+1][..i] == a[..i];
    assert a[..i+1] == a[..i] + [a[i]];
    
    // Use SumPrefix to decompose a[..i+1]
    SumPrefix(a[..i+1], i);
    assert Sum(a[..i+1][..i]) + Sum(a[..i+1][i..]) == Sum(a[..i+1]);
    assert a[..i+1][..i] == a[..i];
    assert a[..i+1][i..] == [a[i]];
    assert Sum([a[i]]) == a[i];
    assert Sum(a[..i]) + a[i] == Sum(a[..i+1]);
    
    result := result + a[i];
    i := i + 1;
    
    assert result == Sum(a[..i]);
  }
  
  assert i == a.Length;
  assert a[..a.Length] == a[..];
  assert result == Sum(a[..]);
  
  // Handle the AllZero postcondition
  if AllZero(a[..]) {
    AllZeroImpliesSumZero(a[..]);
    assert Sum(a[..]) == 0.0;
    assert result == 0.0;
  }
}
// </vc-code>
