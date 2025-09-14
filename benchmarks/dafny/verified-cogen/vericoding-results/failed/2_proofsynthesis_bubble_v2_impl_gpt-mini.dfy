// <vc-preamble>
predicate SortedBetween(a: seq<int>, from: int, to: int)
{
    forall i, j :: from <= i < j < to && 0 <= i < |a| && 0 <= j < |a| ==> a[i] <= a[j]
}

predicate IsReorderOf<T(==)>(r: seq<int>, p: seq<T>, s: seq<T>)
{
    && |r| == |s|
    && (forall i :: 0 <= i < |r| ==> 0 <= r[i] < |r|)
    && (forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j])
    && p == seq(|r|, i requires 0 <= i < |r| => s[r[i]])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): identity sequence, permutation predicate, and lemmas about identity and swaps */
function IdentitySeq(n: int): seq<int> requires n >= 0 { seq(n, i => i) }

predicate IsPermutation(n: int, r: seq<int>) { |r| == n && (forall i :: 0 <= i < n ==> 0 <= r[i] < n) && (forall i, j :: 0 <= i < j < n ==> r[i] != r[j]) }

lemma IdentityIsPermutation(n: int) requires n >= 0 ensures IsPermutation(n, IdentitySeq(n)) { }

lemma SwapPreservesIsPermutation(n: int, r: seq<int>, i: int, j: int, r': seq<int>)
  requires IsPermutation(n, r)
  requires 0 <= i < n && 0 <= j < n
  requires r' == r[i := r[j]][j := r[i]]
  ensures IsPermutation(n, r')
{
}

// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): selection sort with safe seq invariants */
{
  var n := nums.Length;
  ghost var orig := nums[..];
  ghost var r := IdentitySeq(n);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant nums[..] == seq(n, j requires 0 <= j < n => orig[r[j]])
    invariant IsPermutation(n, r)
    invariant SortedBetween(nums[..], 0, i)
    invariant forall a, b :: 0 <= a < i <= b < n ==> nums[a] <= nums[b]
  {
    var minpos := i;
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= minpos < n
      invariant nums[..] == seq(n, t requires 0 <= t < n => orig[r[t]])
      invariant IsPermutation(n, r)
      invariant SortedBetween(nums[..], 0, i)
      invariant forall a, b :: 0 <= a < i <= b < n ==> nums[a] <= nums[b]
    {
      if nums[j] < nums[minpos] {
        minpos := j;
      }
      j := j + 1;
    }
    if minpos != i {
      var tmp := nums[i];
      nums[i] := nums[minpos];
      nums[minpos] := tmp;
      ghost var r0 := r;
      ghost var tmpIdx := r0[minpos];
      ghost var r1 := r0[minpos := r0[i]];
      ghost var r2 := r1[i := tmpIdx];
      r := r2;
      SwapPreservesIsPermutation(n, r0, i, minpos, r2);
    }
    i := i + 1;
  }
  assert SortedBetween(nums[..], 0, n);
  assert IsReorderOf(r, nums[..], orig);
}

// </vc-code>
