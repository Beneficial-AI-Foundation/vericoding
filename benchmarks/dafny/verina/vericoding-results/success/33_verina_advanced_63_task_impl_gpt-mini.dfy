// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define UniqueCount for seq<int> using existence check */
function UniqueCount(s: seq<int>): nat {
  if |s| == 0 then 0
  else var rest := s[1..];
       if exists i :: 0 <= i < |rest| && s[0] == rest[i] then UniqueCount(rest) else UniqueCount(rest) + 1
}

/* helper modified by LLM (iteration 3): prove UniqueCount(s) <= |s| by induction */
lemma UniqueCountLeLength(s: seq<int>) ensures UniqueCount(s) <= |s|
{
  if |s| == 0 {
    // UniqueCount([]) == 0
  } else {
    var rest := s[1..];
    UniqueCountLeLength(rest);
    if exists i :: 0 <= i < |rest| && s[0] == rest[i] {
      // UniqueCount(s) == UniqueCount(rest)
      assert UniqueCount(s) == UniqueCount(rest);
      assert UniqueCount(rest) <= |rest|;
      assert UniqueCount(s) <= |rest|;
      assert |rest| + 1 == |s|;
      assert UniqueCount(s) <= |s|;
    } else {
      assert UniqueCount(s) == UniqueCount(rest) + 1;
      assert UniqueCount(rest) <= |rest|;
      assert UniqueCount(s) <= |rest| + 1;
      assert |rest| + 1 == |s|;
      assert UniqueCount(s) <= |s|;
    }
  }
}

// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(nums: seq<int>) returns (result: nat)
    requires forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
    ensures result <= |nums|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): return number of unique elements using UniqueCount */
  UniqueCountLeLength(nums);
  result := UniqueCount(nums);
}

lemma RemoveDuplicatesSpecSatisfied(nums: seq<int>)
    requires forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
{
  UniqueCountLeLength(nums);
}

// </vc-code>
