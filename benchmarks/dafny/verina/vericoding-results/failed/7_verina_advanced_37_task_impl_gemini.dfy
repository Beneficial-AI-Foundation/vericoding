// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>
method Count(s: seq<int>, val: int) returns (c: nat)
  ensures c == CountOccurrences(s, val)
{
  c := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant c == CountOccurrences(s[..i], val)
  {
    if s[i] == val {
      c := c + 1;
    }
    i := i + 1;
  }
}

lemma UniquenessOfMajority(s: seq<int>, m1: int)
  requires |s| > 0
  requires CountOccurrences(s, m1) > |s| / 2
  ensures forall m2: int :: m2 != m1 ==> CountOccurrences(s, m2) <= |s| / 2
{
  var n := |s|;
  forall m2: int | m2 != m1
    ensures CountOccurrences(s, m2) <= n / 2
  {
    if CountOccurrences(s, m2) > n / 2 {
      var c1 := CountOccurrences(s, m1);
      var c2 := CountOccurrences(s, m2);
      var is1 := set i | 0 <= i < n && s[i] == m1;
      var is2 := set i | 0 <= i < n && s[i] == m2;
      assert is1 * is2 == {};
      var u := is1 + is2;
      assert |u| == |is1| + |is2|;
      assert c1 + c2 <= n;
      if n % 2 == 0 {
        assert c1 >= n/2 + 1 && c2 >= n/2 + 1;
        assert c1 + c2 >= n + 2;
      } else {
        assert c1 >= (n/2) + 1 && c2 >= (n/2) + 1;
        assert c1 + c2 >= 2 * (n/2) + 2;
        assert c1 + c2 >= n + 1;
      }
      assert c1 + c2 > n;
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method MajorityElement(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures var numsSeq := nums[..];
            var n := |numsSeq|;
            CountOccurrences(numsSeq, result) > n / 2 &&
            forall x: int :: x == result || CountOccurrences(numsSeq, x) <= n / 2
// </vc-spec>
// <vc-code>
{
  var n := nums.Length;
  var numsSeq := nums[..];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> CountOccurrences(numsSeq, nums[k]) <= n / 2
  {
    var candidate := nums[i];
    var candidate_count := Count(numsSeq, candidate);
    
    if candidate_count > n / 2 {
        result := candidate;
        UniquenessOfMajority(numsSeq, result);
        return;
    }
    i := i + 1;
  }
  assert false; // This path is unreachable, as a majority element is guaranteed to exist by the postcondition.
}
// </vc-code>
