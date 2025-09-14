

// <vc-helpers>
lemma LemmaCount<T>(a: seq<T>, x: T) returns (count: nat)
  ensures count == multiset(a)[x]
{
  if a == [] {
    count := 0;
  } else {
    var c' := LemmaCount(a[1..], x);
    if a[0] == x {
      count := c' + 1;
    } else {
      count := c';
    }
  }
}

lemma LemmaCountPreserved<T>(a: array<T>, lo: int, hi: int, x: T)
  requires 0 <= lo <= hi <= a.Length
  ensures multiset(a[lo..hi])[x] == multiset(a[..])[x]
  ensures forall i | lo <= i < hi :: a[i] == old(a[i])
{
  assert multiset(a[lo..hi]) == multiset(a[..hi]) - multiset(a[..lo]);
}

lemma LemmaMultisetUnionSeq<T>(s1: seq<T>, s2: seq<T>)
  ensures multiset(s1) + multiset(s2) == multiset(s1 + s2)
{
}

lemma LemmaMultisetSlicePreservation<T>(a: array<T>, j: int, i: int)
  requires 0 <= j <= i <= a.Length
  ensures multiset(a[..j]) + multiset(a[i..]) == multiset(a[..j] + a[i..])
{
}

lemma LemmaArraySliceEquivalence<T>(a: array<T>)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
}

lemma LemmaSortedArrayDistinctPrefix<T(==)>(a: array<T>, j: int) 
  requires forall i, k | 0 <= i < k < a.Length :: a[i] <= a[k]
  requires 0 <= j <= a.Length
  ensures forall i, k | 0 <= i < k < j :: a[i] != a[k]
  ensures forall i | 0 <= i < j :: a[i] in old(a[..])
{
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
// </vc-spec>
// <vc-code>
{
  if nums.Length == 0 {
    num_length := 0;
    return;
  }
  
  var i := 1;
  var j := 1;
  
  while i < nums.Length
    invariant 1 <= j <= i <= nums.Length
    invariant forall k, l | 0 <= k < l < j :: nums[k] != nums[l]
    invariant forall k | 0 <= k < j :: nums[k] in old(nums[..])
    invariant forall k | 0 <= k < nums.Length :: old(nums[k]) in multiset(nums[..j]) + multiset(nums[i..])
    invariant multiset(nums[..j]) + multiset(nums[i..]) == multiset(old(nums[..]))
  {
    if nums[i] != nums[j-1] {
      nums[j] := nums[i];
      j := j + 1;
    }
    i := i + 1;
    
    // Update loop invariants for the changed array
    if j > 0 {
      assert forall k | 0 <= k < j :: nums[k] in old(nums[..]) by {
        if k < j - 1 {
          // nums[k] was already in the prefix
        } else if k == j - 1 {
          // nums[k] is nums[i-1] which is in old(nums[..])
          assert nums[k] == nums[i-1];
        }
      }
    }
  }
  
  num_length := j;
}
// </vc-code>

