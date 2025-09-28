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
/* helper modified by LLM (iteration 5): Changed multiset invariant to a more provable form. */
method merge(a: seq<real>, b: seq<real>) returns (r: seq<real>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures |r| == |a| + |b|
  ensures IsSorted(r)
  ensures IsPermutation(a + b, r)
{
  r := [];
  var i := 0;
  var j := 0;
  while i < |a| && j < |b|
    decreases |a| - i + |b| - j
    invariant 0 <= i <= |a| && 0 <= j <= |b|
    invariant |r| == i + j
    invariant IsSorted(r)
    invariant multiset(r) + multiset(a[i..]) + multiset(b[j..]) == multiset(a) + multiset(b)
    invariant |r| > 0 ==> (i < |a| ==> r[|r|-1] <= a[i])
    invariant |r| > 0 ==> (j < |b| ==> r[|r|-1] <= b[j])
  {
    if a[i] <= b[j] {
      r := r + [a[i]];
      i := i + 1;
    } else {
      r := r + [b[j]];
      j := j + 1;
    }
  }
  r := r + a[i..];
  r := r + b[j..];
}
// </vc-helpers>

// <vc-spec>
method msort(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added an assertion to help prove the permutation property. */
  if |a| <= 1 {
    result := a;
  } else {
    var m := |a| / 2;
    var left := a[..m];
    var right := a[m..];

    assert multiset(a) == multiset(left) + multiset(right);
    
    var sorted_left := msort(left);
    var sorted_right := msort(right);

    result := merge(sorted_left, sorted_right);
  }
}
// </vc-code>
