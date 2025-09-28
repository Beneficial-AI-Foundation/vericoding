// <vc-preamble>
predicate SortedBetween(a: seq<int>, from: int, to: int)
    requires 0 <= from <= to <= |a|
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

predicate IsReorderOf<T(==)>(r: seq<int>, p: seq<T>, s: seq<T>)
    requires |r| == |p| && |r| == |s|
{
    && |r| == |s|
    && (forall i :: 0 <= i < |r| ==> 0 <= r[i] < |s|)
    && (forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j])
    && (forall i :: 0 <= i < |r| ==> p[i] == s[r[i]])
}
// </vc-preamble>

// <vc-helpers>
predicate IsPermutation(perm: seq<int>, n: int)
{
  |perm| == n && (forall i :: 0 <= i < n ==> 0 <= perm[i] < n) && (forall i,j :: 0 <= i < j < n ==> perm[i] != perm[j])
}

lemma ProveIsReorderOf(nums: array<int>, original: seq<int>, perm: array<int>)
  requires nums.Length == perm.Length && |original| == nums.Length
  requires IsPermutation(perm[..], nums.Length)
  requires forall i :: 0 <= i < nums.Length ==> nums[i] == original[perm[i]]
  ensures IsReorderOf(perm[..], nums[..], original)
{
  var r := perm[..];
  var p := nums[..];
  var s := original;
  assert |r| == |p| == |s|;
  assert forall i :: 0 <= i < |r| ==> 0 <= r[i] < |s|;
  assert forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j];
  assert forall i :: 0 <= i < |r| ==> p[i] == s[r[i]];
}

/* helper modified by LLM (iteration 5): Updated lemma body to use == for |r| assertions */
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: |r| == nums.Length && IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added ghost original for invariants, added missing invariants for permutation and element equivalence */
  ghost var original: seq<int> := nums[..];
  var perm := new int[nums.Length];
  forall i | 0 <= i < nums.Length { perm[i] := i; }
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant SortedBetween(nums[..], nums.Length - i, nums.Length)
    invariant multiset(nums[..]) == multiset(original)
    invariant IsPermutation(perm[..], nums.Length)
    invariant forall k :: 0 <= k < nums.Length ==> nums[k] == original[perm[k]]
  {
    var j := 0;
    while j < nums.Length - i - 1
      invariant 0 <= j <= nums.Length - i - 1
      invariant forall k :: 0 <= k < j ==> nums[k] <= nums[k+1]
      invariant SortedBetween(nums[..], nums.Length - i, nums.Length)
      invariant multiset(nums[..]) == multiset(original)
      invariant IsPermutation(perm[..], nums.Length)
      invariant forall k :: 0 <= k < nums.Length ==> nums[k] == original[perm[k]]
    {
      if nums[j] > nums[j+1]
      {
        nums[j], nums[j+1] := nums[j+1], nums[j];
        perm[j], perm[j+1] := perm[j+1], perm[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  ProveIsReorderOf(nums, original, perm);
}
// </vc-code>
