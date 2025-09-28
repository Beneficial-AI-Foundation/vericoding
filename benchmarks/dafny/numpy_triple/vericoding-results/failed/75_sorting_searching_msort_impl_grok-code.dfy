// <vc-preamble>
// Helper predicate to check if a sequence is sorted in ascending order
ghost predicate IsSorted(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if two sequences are permutations of each other
ghost predicate IsPermutation(a: seq<real>, b: seq<real>)
{
  multiset(a) == multiset(b)
}

// Main method specification for msort
// </vc-preamble>

// <vc-helpers>
method merge(a: seq<real>, b: seq<real>) returns (c: seq<real>)
  requires IsSorted(a) && IsSorted(b)
  ensures IsSorted(c)
  ensures IsPermutation(a + b, c)
  ensures |c| == |a| + |b|
{
  c := [];
  var i, j := 0, 0;
  while i < |a| || j < |b|
    decreases |a| - i + |b| - j
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant IsSorted(c)
    invariant IsPermutation(c, a[..i] + b[..j])
    invariant |c| == i + j
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      c := c + [a[i]];
      i := i + 1;
    } else {
      c := c + [b[j]];
      j := j + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method msort(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): implementing recursive merge sort with proper ensures */
{
  if |a| <= 1 {
    result := a;
  } else {
    var mid := |a| / 2;
    var left := msort(a[..mid]);
    var right := msort(a[mid..]);
    result := merge(left, right);
  }
}
// </vc-code>
