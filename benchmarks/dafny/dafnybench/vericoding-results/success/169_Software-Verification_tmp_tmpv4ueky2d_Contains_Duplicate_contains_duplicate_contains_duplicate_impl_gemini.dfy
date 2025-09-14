// <vc-preamble>
predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}
// </vc-preamble>

// <vc-helpers>
predicate is_in_spec(x: int, s: seq<int>) {
    exists i :: 0 <= i < |s| && s[i] == x
}

lemma NotInImpliesDistinct(s: seq<int>, x: int)
    requires distinct(s)
    requires forall k :: 0 <= k < |s| ==> s[k] != x
    ensures distinct(s + [x])
{}
// </vc-helpers>

// <vc-spec>
method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
// </vc-spec>
// <vc-code>
{
  var i := 1;
  while i < |nums|
    invariant 1 <= i <= |nums|
    invariant distinct(nums[..i])
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant distinct(nums[..i])
      invariant forall k :: 0 <= k < j ==> nums[k] != nums[i]
    {
      if nums[j] == nums[i] {
        result := false;
        return;
      }
      j := j + 1;
    }
    NotInImpliesDistinct(nums[..i], nums[i]);
    i := i + 1;
  }
  result := true;
}
// </vc-code>
