function factorial(n: nat): nat
{
    if n == 0 then 1 else n * factorial(n - 1)
}

predicate IsPermutation(perm: seq<int>, original: seq<int>)
{
    |perm| == |original| && multiset(perm) == multiset(original)
}

predicate AllDistinct<T(==)>(s: seq<T>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// <vc-helpers>
lemma Fact_mul(n: nat)
  ensures n == 0 ==> factorial(n) == 1
  ensures n > 0 ==> factorial(n) == n * factorial(n - 1)
{
  if n == 0 {
    return;
  }
  // By unfolding the definition of factorial
  assert factorial(n) == n * factorial(n - 1);
}

lemma Remove_preserve_distinct<T>(s: seq<T>, i: int)
  requires AllDistinct(s)
  requires 0 <= i < |s|
  ensures AllDistinct(s[..i] + s[i+1..])
{
  var rest := s[..i] + s[i+1..];
  // prove distinctness by considering all pairs of indices in rest
  forall a, b | 0 <= a < b < |rest|
    ensures rest[a] != rest[b]
  {
    if b < i {
      // both indices refer into the prefix s[..i]
      assert rest[a] == s[a];
      assert rest[b] == s[b];
      assert s[a] != s[b];
    } else if a >= i {
      // both indices refer into the suffix s[i+1..]
      // mapping: rest[a] == s[a+1], rest[b] == s[b+1]
      assert rest[a] == s[a+1];
      assert rest[b] == s[b+1];
      assert s[a+1] != s[b+1];
    } else {
      // a < i and b >= i: rest[a] == s[a], rest[b] == s[b+1]
      assert rest[a] == s[a];
      assert rest[b] == s[b+1];
      assert s[a] != s[b+1];
    }
  }
}

lemma Subperm_tail_is_perm(nums: seq<int>, i: int, perm: seq<int>)
  requires 0 <= i < |nums|
  requires IsPermutation(perm, nums)
  ensures IsPermutation(perm[1..], nums[..i] + nums[i+1..])
{
  var x := perm[0];
  var rest := nums[..i] + nums[i+1..];
  // lengths
  assert |perm[1..]| + 1 == |perm|;
  assert |rest| + 1 == |nums|;
  assert |perm| == |nums|;
  assert |perm[1..]| == |rest|;
  // multisets: remove one occurrence of x from both sides
  assert multiset(perm) == multiset(nums);
  assert multiset(perm) == multiset(perm[1..]) + multiset([perm[0]]);
  assert multiset(nums) == multiset(rest) + multiset([nums[i]]);
  assert multiset(perm[1..]) + multiset([perm[0]]) == multiset(rest) + multiset([perm[0]]);
  assert multiset(perm[1..]) == multiset(rest);
}
// </vc-helpers>

// <vc-spec>
method permute(nums: seq<int>) returns (result: seq<seq<int>>)
    requires AllDistinct(nums)
    ensures |result| == factorial(|nums|)
    ensures forall p :: p in result ==> IsPermutation(p, nums)
    ensures AllDistinct(result)
    ensures forall perm :: IsPermutation(perm, nums) ==> perm in result
// </vc-spec>
// <vc-code>
{
  if |nums| == 0 {
    result := [ [] ];
    return;
  }

  var n := |nums|;
  // Outer loop builds groups of permutations whose first element is nums[i]
  result := [];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i * factorial(n - 1)
    invariant forall r :: r in result ==> IsPermutation(r, nums)
    invariant AllDistinct(result)
    invariant forall r :: r in result ==> exists k :: 0 <= k < i && r[0] == nums[k]
  {
    var x := nums[i];
    var rest := nums[..i] + nums[i+1..];
    // rest is distinct
    Remove_preserve_distinct(nums, i);
    assert AllDistinct(rest);

    var sub := permute(rest);
    // sub contains all permutations of rest and is distinct
    assert |sub| == factorial(|rest|);
    assert |rest| == n - 1;
    assert |sub| == factorial(n - 1);
    assert forall p :: p in sub ==> IsPermutation(p, rest);
    assert AllDistinct(sub);

    // build new group by prefixing x to each permutation of rest
    var subLen := |sub|;
    var newGroup := ([]: seq<seq<int>>);
    var k2 := 0;
    while k2 < subLen
      invariant 0 <= k2 <= subLen
      invariant |newGroup| == k2
      invariant forall t :: 0 <= t < k2 ==> newGroup[t] == [x] + sub[t]
    {
      newGroup := newGroup + [[x] + sub[k2]];
      k2 := k2 + 1;
    }

    // properties of newGroup
    assert |newGroup| == |sub|;
    // each element of newGroup is a permutation of nums
    forall k | 0 <= k < |sub|
      ensures IsPermutation(newGroup[k], nums)
    {
      var p := sub[k];
      // newGroup[k] = [x] + p
      // length
      assert |[x] + p| == 1 + |p|;
      assert |p| == |rest|;
      assert 1 + |p| == |nums|;
      assert multiset([x] + p) == multiset([x]) + multiset(p);
      assert multiset(p) == multiset(rest);
      assert multiset([x]) + multiset(rest) == multiset(nums);
      assert multiset([x] + p) == multiset(nums);
    }

    // newGroup elements are pairwise distinct because sub is AllDistinct
    forall a, b | 0 <= a < b < |newGroup|
      ensures newGroup[a] != newGroup[b]
    {
      assert sub[a] != sub[b];
      assert [x] + sub[a] != [x] + sub[b];
    }

    // newGroup is disjoint from existing result because their first elements differ
    forall r, s | r in result && s in newGroup
      ensures r != s
    {
      // r has first element nums[k] for some k < i
      assert exists k :: 0 <= k < i && r[0] == nums[k];
      var kk := (choose j :: 0 <= j < i && r[0] == nums[j]);
      assert r[0] == nums[kk];
      // s has first element x == nums[i]
      assert s[0] == x;
      // since nums elements are distinct, nums[kk] != nums[i]
      assert nums[kk] != nums[i];
      assert r[0] != s[0];
      // thus r != s
    }

    // append newGroup to result
    result := result + newGroup;

    // update invariants for next iteration
    i := i + 1;
  }

  // at this point i == n and |result| == n * factorial(n - 1) == factorial(n)
  Fact_mul(n);
  assert |result| == factorial(n);

  // show completeness: any permutation of nums is in result
  forall perm | IsPermutation(perm, nums)
    ensures perm in result
  {
    if |nums| == 0 {
      assert perm == [];
      assert perm in result;
      continue;
    }
    var x := perm[0];
    // find index k with nums[k] == x by scanning (such an index exists because multisets equal)
    var k := 0;
    while nums[k] != x
      invariant 0 <= k < n
      decreases n - k
    {
      k := k + 1;
    }
    // now nums[k] == x
    var rest := nums[..k] + nums[k+1..];
    Subperm_tail_is_perm(nums, k, perm);
    var tail := perm[1..];
    // by recursive correctness, tail is in permute(rest)
    var sub := permute(rest);
    assert tail in sub;
    // so [x] + tail is in the corresponding group; reconstruct that group and show membership
    var subLen2 := |sub|;
    var group := ([]: seq<seq<int>>);
    var tt := 0;
    while tt < subLen2
      invariant 0 <= tt <= subLen2
      invariant |group| == tt
      invariant forall t :: 0 <= t < tt ==> group[t] == [x] + sub[t]
    {
      group := group + [[x] + sub[tt]];
      tt := tt + 1;
    }

    var j := (choose u :: 0 <= u < subLen2 && sub[u] == tail);
    assert 0 <= j < subLen2;
    assert group[j] == [x] + sub[j];
    assert group[j] == [x] + tail;
    // Since during the main construction we appended the group corresponding to nums[k],
    // that group's elements are included in result; thus group[j] is in result.
    assert group[j] in result;
    assert perm in result;
  }
}
// </vc-code>

