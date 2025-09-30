// <vc-preamble>
/*
 * Counts the number of non-zero values in a sequence of integers.
 * 
 * This function counts exactly those elements that are not equal to zero.
 * The result is always between 0 and the length of the sequence (inclusive).
 */

// Helper predicate to check if all elements in a sequence are zero
ghost predicate AllZero(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] == 0
}

// Helper predicate to check if all elements in a sequence are non-zero  
ghost predicate AllNonZero(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] != 0
}

// Helper predicate to check if there exists a non-zero element
ghost predicate ExistsNonZero(s: seq<int>)
{
    exists i :: 0 <= i < |s| && s[i] != 0
}

// Helper predicate to check if there exists a zero element
ghost predicate ExistsZero(s: seq<int>)
{
    exists i :: 0 <= i < |s| && s[i] == 0
}

// Helper function to count non-zero elements (for specification purposes)
ghost function CountNonZeroElements(s: seq<int>): nat
{
    if |s| == 0 then 0
    else (if s[0] != 0 then 1 else 0) + CountNonZeroElements(s[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Unfold CountNonZeroElements for non-empty sequences */
lemma CountNonZero_Cons(s: seq<int>)
  requires |s| >= 1
  ensures CountNonZeroElements(s) == (if s[0] != 0 then 1 else 0) + CountNonZeroElements(s[1..])
{
  assert CountNonZeroElements(s) == (if s[0] != 0 then 1 else 0) + CountNonZeroElements(s[1..]);
}

/* helper modified by LLM (iteration 5): CountNonZeroElements <= length */
lemma CountNonZero_Le_Length(s: seq<int>)
  ensures CountNonZeroElements(s) <= |s|
  decreases |s|
{
  if |s| == 0 {
    assert CountNonZeroElements(s) == 0;
  } else {
    var tail := s[1..];
    // Inductive hypothesis on the tail
    CountNonZero_Le_Length(tail);
    // Unfold head case
    CountNonZero_Cons(s);
    if s[0] != 0 {
      assert CountNonZeroElements(s) == 1 + CountNonZeroElements(tail);
      assert CountNonZeroElements(tail) <= |tail|;
      assert 1 + CountNonZeroElements(tail) <= 1 + |tail|;
      assert 1 + |tail| == |s|;
    } else {
      assert CountNonZeroElements(s) == CountNonZeroElements(tail);
      assert CountNonZeroElements(tail) <= |tail|;
      assert CountNonZeroElements(tail) <= |s|;
    }
  }
}

/* helper modified by LLM (iteration 5): Empty sequence has zero non-zero elements */
lemma CountNonZero_Empty(s: seq<int>)
  requires |s| == 0
  ensures CountNonZeroElements(s) == 0
{
  assert CountNonZeroElements(s) == 0;
}

/* helper modified by LLM (iteration 5): If all elements are zero, count is 0 */
lemma CountNonZero_AllZero(s: seq<int>)
  ensures AllZero(s) ==> CountNonZeroElements(s) == 0
  decreases |s|
{
  if |s| == 0 {
    // trivial
  } else {
    if AllZero(s) {
      CountNonZero_Cons(s);
      // From AllZero(s) we have s[0] == 0 and AllZero(s[1..])
      assert s[0] == 0;
      assert AllZero(s[1..]);
      CountNonZero_AllZero(s[1..]);
      assert CountNonZeroElements(s) == CountNonZeroElements(s[1..]);
      assert CountNonZeroElements(s[1..]) == 0;
      assert CountNonZeroElements(s) == 0;
    }
  }
}

/* helper modified by LLM (iteration 5): If all elements are non-zero, count equals length */
lemma CountNonZero_AllNonZero(s: seq<int>)
  ensures AllNonZero(s) ==> CountNonZeroElements(s) == |s|
  decreases |s|
{
  if |s| == 0 {
    // trivial
  } else {
    if AllNonZero(s) {
      CountNonZero_Cons(s);
      assert s[0] != 0;
      assert AllNonZero(s[1..]);
      CountNonZero_AllNonZero(s[1..]);
      assert CountNonZeroElements(s) == 1 + CountNonZeroElements(s[1..]);
      assert CountNonZeroElements(s[1..]) == |s|-1;
      assert 1 + (|s|-1) == |s|;
    }
  }
}

/* helper modified by LLM (iteration 5): Existence of a non-zero implies count > 0 */
lemma CountNonZero_ExistsNonZero(s: seq<int>)
  ensures ExistsNonZero(s) ==> CountNonZeroElements(s) > 0
  decreases |s|
{
  if |s| == 0 {
    // impossible when ExistsNonZero(s) holds
  } else {
    if ExistsNonZero(s) {
      CountNonZero_Cons(s);
      if s[0] != 0 {
        assert CountNonZeroElements(s) == 1 + CountNonZeroElements(s[1..]);
        assert 1 + CountNonZeroElements(s[1..]) > 0;
      } else {
        // s[0] == 0, so existence must be in tail
        assert ExistsNonZero(s[1..]);
        CountNonZero_ExistsNonZero(s[1..]);
        assert CountNonZeroElements(s) == CountNonZeroElements(s[1..]);
        assert CountNonZeroElements(s[1..]) > 0;
      }
    }
  }
}

/* helper modified by LLM (iteration 5): Existence of a zero implies count < length */
lemma CountNonZero_ExistsZero(s: seq<int>)
  ensures ExistsZero(s) ==> CountNonZeroElements(s) < |s|
  decreases |s|
{
  if |s| == 0 {
    // impossible when ExistsZero(s) holds
  } else {
    if ExistsZero(s) {
      CountNonZero_Cons(s);
      if s[0] == 0 {
        // count equals tail's count
        CountNonZero_Le_Length(s[1..]);
        assert CountNonZeroElements(s) == CountNonZeroElements(s[1..]);
        assert CountNonZeroElements(s[1..]) <= |s|-1;
        assert CountNonZeroElements(s) < |s|;
      } else {
        // zero must be in tail
        assert ExistsZero(s[1..]);
        CountNonZero_ExistsZero(s[1..]);
        CountNonZero_Cons(s);
        assert CountNonZeroElements(s) == 1 + CountNonZeroElements(s[1..]);
        assert CountNonZeroElements(s[1..]) < |s|-1;
        assert 1 + CountNonZeroElements(s[1..]) < 1 + (|s|-1);
        assert CountNonZeroElements(s) < |s|;
      }
    }
  }
}

// </vc-helpers>

// <vc-spec>
method CountNonZero(a: seq<int>) returns (count: nat)
    ensures count <= |a|
    ensures |a| == 0 ==> count == 0
    ensures AllZero(a) ==> count == 0
    ensures AllNonZero(a) ==> count == |a|
    ensures ExistsNonZero(a) ==> count > 0
    ensures ExistsZero(a) ==> count < |a|
    ensures count == CountNonZeroElements(a)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): loop implementation with lemma calls; fix lemmas calls to use suffix */
  var n := |a|;
  var i := 0;
  count := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= count <= CountNonZeroElements(a)
    invariant count + CountNonZeroElements(a[i..]) == CountNonZeroElements(a)
    decreases n - i
  {
    var s := a[i..];
    CountNonZero_Cons(s);
    if s[0] != 0 {
      count := count + 1;
    }
    i := i + 1;
    assert a[i..] == s[1..];
    assert count + CountNonZeroElements(a[i..]) == CountNonZeroElements(a);
  }
  // remaining suffix is empty
  assert n == |a|;
  assert |a[n..]| == 0;
  assert CountNonZeroElements(a[n..]) == 0;
  assert count == CountNonZeroElements(a);
  // Call lemmas to help verifier prove postconditions
  CountNonZero_Le_Length(a);
  CountNonZero_Empty(a[n..]);
  CountNonZero_AllZero(a);
  CountNonZero_AllNonZero(a);
  CountNonZero_ExistsNonZero(a);
  CountNonZero_ExistsZero(a);
}

// </vc-code>
