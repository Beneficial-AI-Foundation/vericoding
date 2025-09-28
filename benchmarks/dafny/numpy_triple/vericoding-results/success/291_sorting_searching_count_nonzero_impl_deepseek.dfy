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
function RecursiveCount(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] != 0 then 1 else 0) + RecursiveCount(s[1..])
}

lemma RecursiveCountEqualsSpec(s: seq<int>)
  ensures RecursiveCount(s) == CountNonZeroElements(s)
  decreases |s|
{
  if |s| != 0 {
    RecursiveCountEqualsSpec(s[1..]);
  }
}

lemma RecursiveCountBounds(s: seq<int>)
  ensures RecursiveCount(s) <= |s|
  decreases |s|
{
  if |s| == 0 {
  } else {
    RecursiveCountBounds(s[1..]);
  }
}

lemma RecursiveCountZeroImplies(count: nat, s: seq<int>)
  requires count == RecursiveCount(s)
  ensures AllZero(s) ==> count == 0
  ensures AllNonZero(s) ==> count == |s|
  ensures ExistsNonZero(s) ==> count > 0
  ensures ExistsZero(s) ==> count < |s|
  decreases |s|
{
  if |s| == 0 {
  } else {
    if AllZero(s) {
      assert s[0] == 0;
      RecursiveCountZeroImplies(RecursiveCount(s[1..]), s[1..]);
    }
    if AllNonZero(s) {
      assert s[0] != 0;
      RecursiveCountZeroImplies(RecursiveCount(s[1..]), s[1..]);
    }
    if ExistsNonZero(s) {
      RecursiveCountZeroImplies(RecursiveCount(s[1..]), s[1..]);
    }
    if ExistsZero(s) {
      RecursiveCountZeroImplies(RecursiveCount(s[1..]), s[1..]);
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
  /* code modified by LLM (iteration 4): Add necessary lemmas to prove all postconditions */
  var result := RecursiveCount(a);
  RecursiveCountEqualsSpec(a);
  RecursiveCountBounds(a);
  RecursiveCountZeroImplies(result, a);
  count := result;
}
// </vc-code>
