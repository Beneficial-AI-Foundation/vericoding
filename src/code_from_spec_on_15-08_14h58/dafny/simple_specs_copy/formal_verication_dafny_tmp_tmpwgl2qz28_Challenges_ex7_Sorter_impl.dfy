//ATOM
// see pdf 'ex6 & 7 documentation' for excercise question

datatype Bases = A | C | G | T


//ATOM

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{
  forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}


//ATOM

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{
  first == second ||
  first == A || 
  (first == C && (second == G || second == T)) || 
  (first == G && second == T) ||
  second == T
}


//ATOM

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
  /* code modified by LLM (iteration 1): implemented actual swap instead of using assume statements */
  t := s[x := s[y]][y := s[x]];
}


//IMPL 

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases)
{
  sobases := bases;
  var i := 1;
  
  while i < |sobases|
    invariant 1 <= i <= |sobases|
    invariant |sobases| == |bases|
    invariant multiset(sobases) == multiset(bases)
    /* code modified by LLM (iteration 2): keep only the invariant that can be maintained - elements 0..i-1 are sorted */
    invariant bordered(sobases[..i])
  {
    var j := i;
    /* code modified by LLM (iteration 2): simplified inner loop invariants to only track what we can prove */
    while j > 0 && !below(sobases[j-1], sobases[j])
      invariant 0 <= j <= i
      invariant |sobases| == |bases|
      invariant multiset(sobases) == multiset(bases)
      invariant forall x, y :: 0 <= x < y < j ==> below(sobases[x], sobases[y])
      invariant j < i ==> forall k :: j < k <= i ==> below(sobases[j], sobases[k])
      invariant bordered(sobases[..j])
    {
      sobases := Exchanger(sobases, j-1, j);
      j := j - 1;
    }
    /* code modified by LLM (iteration 2): added assertion and proof that the preconditions for ExtendBordered are met */
    assert j == 0 || below(sobases[j-1], sobases[j]);
    assert bordered(sobases[..i]); // This follows from the loop invariant and the properties maintained
    
    /* code modified by LLM (iteration 2): prove that we can extend the bordered property */
    if i > 0 {
      assert below(sobases[i-1], sobases[i]) by {
        if j == 0 {
          // All elements from 0 to i have been properly arranged
          assert bordered(sobases[..i+1]);
        } else {
          // j > 0 and the loop terminated because below(sobases[j-1], sobases[j]) holds
          // Since j == i, we have below(sobases[i-1], sobases[i])
          assert j == i;
          assert below(sobases[j-1], sobases[j]);
        }
      }
    }
    
    /* code modified by LLM (iteration 2): call helper lemma with proven preconditions */
    ExtendBordered(sobases, i);
    assert bordered(sobases[..i+1]);
    i := i + 1;
  }
}

/* code modified by LLM (iteration 2): added helper lemma to prove that borderness can be extended */
lemma ExtendBordered(s: seq<Bases>, i: nat)
  requires 1 <= i < |s|
  requires bordered(s[..i])
  requires i == 0 || (i > 0 && below(s[i-1], s[i]))
  ensures bordered(s[..i+1])
{
  // The lemma proves that if s[..i] is bordered and s[i-1] <= s[i],
  // then s[..i+1] is also bordered
  assert s[..i+1] == s[..i] + [s[i]];
  
  forall x, y | 0 <= x < y < i+1
    ensures below(s[x], s[y])
  {
    if y < i {
      // Both indices are in the already sorted part
      assert below(s[x], s[y]);
    } else {
      // y == i, so we need to show below(s[x], s[i])
      assert y == i;
      if x == i - 1 {
        // This is the condition we required
        assert below(s[x], s[i]);
      } else {
        // x < i - 1, so we can use transitivity through the bordered property
        assert x < i - 1 < i;
        assert below(s[x], s[i-1]); // from bordered(s[..i])
        assert below(s[i-1], s[i]); // from our requirement
        // We need to prove transitivity of below
        BelowTransitive(s[x], s[i-1], s[i]);
      }
    }
  }
}

/* code modified by LLM (iteration 2): added helper lemma to prove transitivity of below relation */
lemma BelowTransitive(a: Bases, b: Bases, c: Bases)
  requires below(a, b) && below(b, c)
  ensures below(a, c)
{
  // Prove transitivity by case analysis on the bases
  // Given the definition of below, we need to check all cases
  if a == c {
    // Trivially true
  } else if a == A {
    // A is below everything, so below(A, c) is true
  } else if c == T {
    // Everything is below T, so below(a, T) is true  
  } else {
    // Check remaining cases based on the ordering A < C < G < T
    // The below relation is reflexive and transitive by construction
  }
}