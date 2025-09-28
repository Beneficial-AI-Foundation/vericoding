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
predicate IsPermutation(p: seq<int>, size: int)
{
  && |p| == size
  && forall i :: 0 <= i < size ==> ((0 <= p[i]) && (p[i] < size))
  && forall i, j :: 0 <= i < j < size ==> p[i] != p[j]
}

/* helper modified by LLM (iteration 5): Added parentheses to fixwarning, kept expanded for better verification */
// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Used sequence for old values to avoid warnings, expanded permutation invariants to avoid cyclic dependency */
  var n := nums.Length;
  var old_nums := nums[..];
  var perm := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> perm[k] == k
    invariant forall k :: 0 <= k < i ==> 0 <= perm[k] < n
  {
    perm[i] := i;
    i := i + 1;
  }
  var pass := 0;
  while pass < n
    invariant 0 <= pass <= n
    invariant forall i :: 0 <= i < n ==> nums[i] == old_nums[perm[i]]
    invariant |perm| == n
    invariant forall i :: 0 <= i < n ==> 0 <= perm[i] < n
    invariant forall i, j :: 0 <= i < j < n ==> perm[i] != perm[j]
    invariant multiset(nums[..n]) == multiset(old_nums)
    invariant SortedBetween(nums[..], n - pass, n)
  {
    var j := 0;
    while j < n - pass - 1
      invariant 0 <= j <= n - pass - 1
      invariant forall i :: 0 <= i < n ==> nums[i] == old_nums[perm[i]]
      invariant |perm| == n
      invariant forall i :: 0 <= i < n ==> 0 <= perm[i] < n
      invariant forall i, j :: 0 <= i < j < n ==> perm[i] != perm[j]
      invariant multiset(nums[..n]) == multiset(old_nums)
      invariant SortedBetween(nums[..], n - pass, n)
    {
      if nums[j] > nums[j+1] {
        var temp := nums[j];
        nums[j] := nums[j+1];
        nums[j+1] := temp;
        var ptemp := perm[j];
        perm[j] := perm[j+1];
        perm[j+1] := ptemp;
      }
      j := j + 1;
    }
    pass := pass + 1;
  }
}
// </vc-code>
