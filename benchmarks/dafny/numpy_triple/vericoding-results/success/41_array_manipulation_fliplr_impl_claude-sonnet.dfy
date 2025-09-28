// <vc-preamble>
/*
 * Specification for numpy.fliplr: Reverse the order of elements along axis 1 (left/right).
 * This function flips a 2D matrix horizontally, reversing the column order in each row
 * while preserving the row order and the elements within each row.
 */

// Predicate to check if a 2D matrix is well-formed (rectangular)
predicate IsWellFormedMatrix<T>(m: seq<seq<T>>)
{
    |m| > 0 && 
    (forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|) &&
    |m[0]| > 0
}

// Predicate to check if two rows contain the same multiset of elements
predicate SameElements<T(==)>(row1: seq<T>, row2: seq<T>)
{
    multiset(row1) == multiset(row2)
}
// </vc-preamble>

// <vc-helpers>
// Helper function to reverse a sequence
function ReverseSeq<T>(s: seq<T>): seq<T>
{
    if |s| == 0 then []
    else ReverseSeq(s[1..]) + [s[0]]
}

/* helper modified by LLM (iteration 3): added ensures clause for sequence length */
// Lemma to prove that reverse preserves length
lemma ReversePreservesLength<T>(s: seq<T>)
    ensures |ReverseSeq(s)| == |s|
{
    if |s| == 0 {
        // Base case: empty sequence
    } else {
        // Inductive case
        ReversePreservesLength(s[1..]);
        assert |ReverseSeq(s)| == |ReverseSeq(s[1..]) + [s[0]]|;
        assert |ReverseSeq(s[1..]) + [s[0]]| == |ReverseSeq(s[1..])| + 1;
    }
}

/* helper modified by LLM (iteration 3): fixed multiset assertion and indexing bounds */
// Lemma to prove that reversing preserves multiset
lemma ReversePreservesMultiset<T>(s: seq<T>)
    ensures multiset(ReverseSeq(s)) == multiset(s)
{
    if |s| == 0 {
        // Base case: empty sequence
    } else {
        // Inductive case
        ReversePreservesMultiset(s[1..]);
        assert multiset(ReverseSeq(s)) == multiset(ReverseSeq(s[1..]) + [s[0]]);
        assert multiset(ReverseSeq(s[1..]) + [s[0]]) == multiset(ReverseSeq(s[1..])) + multiset([s[0]]);
        assert multiset(ReverseSeq(s[1..])) == multiset(s[1..]);
        assert multiset(s[1..]) + multiset([s[0]]) == multiset([s[0]] + s[1..]);
        assert [s[0]] + s[1..] == s;
    }
}

// Lemma to prove that reverse has the correct indexing
lemma ReverseIndexing<T>(s: seq<T>)
    requires |s| > 0
    ensures |ReverseSeq(s)| == |s|
    ensures forall j :: 0 <= j < |s| ==> ReverseSeq(s)[j] == s[|s|-1-j]
{
    ReversePreservesLength(s);
    if |s| == 1 {
        // Base case
        assert ReverseSeq(s) == [s[0]];
        assert |ReverseSeq(s)| == 1;
    } else {
        // Inductive case
        ReverseIndexing(s[1..]);
        var rev := ReverseSeq(s);
        assert rev == ReverseSeq(s[1..]) + [s[0]];
        assert |rev| == |s|;
        forall j | 0 <= j < |s| ensures rev[j] == s[|s|-1-j] {
            if j < |s| - 1 {
                assert rev[j] == ReverseSeq(s[1..])[j];
                assert ReverseSeq(s[1..])[j] == s[1..][|s[1..]|-1-j];
                assert s[1..][|s[1..]|-1-j] == s[|s|-1-j];
            } else {
                assert j == |s| - 1;
                assert rev[j] == s[0];
                assert s[|s|-1-j] == s[0];
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method FlipLR(m: seq<seq<real>>) returns (result: seq<seq<real>>)
    requires IsWellFormedMatrix(m)
    requires |m| >= 1 && |m[0]| >= 1  // At least 2D matrix
    ensures IsWellFormedMatrix(result)
    ensures |result| == |m|
    ensures |result[0]| == |m[0]|
    // Element mapping: result[i][j] == m[i][cols-1-j]
    ensures forall i :: 0 <= i < |result| ==>
        forall j :: 0 <= j < |result[i]| ==>
            result[i][j] == m[i][|m[i]|-1-j]
    // Row preservation: each row contains the same elements
    ensures forall i :: 0 <= i < |result| ==>
        SameElements(result[i], m[i])
    // Dimensions are preserved
    ensures forall i :: 0 <= i < |result| ==>
        |result[i]| == |m[i]|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): strengthened loop invariant to maintain bounds */
  result := [];
  
  var i := 0;
  while i < |m|
    invariant 0 <= i <= |m|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |m[k]|
    invariant forall k :: 0 <= k < i ==> SameElements(result[k], m[k])
    invariant forall k :: 0 <= k < i ==> 
        forall j :: 0 <= j < |result[k]| ==> 
            result[k][j] == m[k][|m[k]|-1-j]
  {
    var reversedRow := ReverseSeq(m[i]);
    ReversePreservesLength(m[i]);
    ReversePreservesMultiset(m[i]);
    if |m[i]| > 0 {
        ReverseIndexing(m[i]);
    }
    result := result + [reversedRow];
    i := i + 1;
  }
}
// </vc-code>
