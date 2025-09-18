// <vc-preamble>
function CountOccurrences(nums: seq<int>, x: int): nat
    decreases |nums|
{
    if |nums| == 0 then
        0
    else
        var first := nums[0];
        var restCount := CountOccurrences(nums[1..], x);
        if first == x then
            restCount + 1
        else
            restCount
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove sum of counts of two distinct values <= length */
lemma CountOccurrences_Disjoint_Bound(nums: seq<int>, a: int, b: int)
  requires a != b
  ensures CountOccurrences(nums,a) + CountOccurrences(nums,b) <= |nums|
  decreases |nums|
{
  if |nums| == 0 {
    assert CountOccurrences(nums,a) + CountOccurrences(nums,b) == 0;
  } else {
    var first := nums[0];
    var rest := nums[1..];
    CountOccurrences_Disjoint_Bound(rest,a,b);
    assert |nums| == |rest| + 1;
    if first == a {
      assert CountOccurrences(nums,a) == CountOccurrences(rest,a) + 1;
      assert CountOccurrences(nums,b) == CountOccurrences(rest,b);
    } else if first == b {
      assert CountOccurrences(nums,a) == CountOccurrences(rest,a);
      assert CountOccurrences(nums,b) == CountOccurrences(rest,b) + 1;
    } else {
      assert CountOccurrences(nums,a) == CountOccurrences(rest,a);
      assert CountOccurrences(nums,b) == CountOccurrences(rest,b);
    }
    assert CountOccurrences(rest,a) + CountOccurrences(rest,b) <= |rest|;
    assert CountOccurrences(nums,a) + CountOccurrences(nums,b) <= |rest| + 1;
    assert CountOccurrences(nums,a) + CountOccurrences(nums,b) <= |nums|;
  }
}

/* helper modified by LLM (iteration 2): show majority element is unique above half */
lemma Majority_NoOtherGreater(nums: seq<int>, m: int)
  requires CountOccurrences(nums,m) > |nums|/2
  ensures forall x :: x != m ==> CountOccurrences(nums,x) <= |nums|/2
{
  var n := |nums|;
  if exists x :: x != m && CountOccurrences(nums,x) > n/2 {
    var x :| x != m && CountOccurrences(nums,x) > n/2;
    CountOccurrences_Disjoint_Bound(nums,m,x);
    assert CountOccurrences(nums,m) + CountOccurrences(nums,x) <= n;
    assert CountOccurrences(nums,m) > n/2;
    assert CountOccurrences(nums,x) > n/2;
    assert CountOccurrences(nums,m) + CountOccurrences(nums,x) > n;
    assert false;
  }
}

// </vc-helpers>

// <vc-spec>
method MajorityElement(nums: seq<int>) returns (result: int)
    requires 
        |nums| > 0 &&
        exists x :: CountOccurrences(nums, x) > |nums| / 2
    ensures 
        CountOccurrences(nums, result) > |nums| / 2 &&
        forall x :: x != result ==> CountOccurrences(nums, x) <= |nums| / 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): choose majority witness and apply lemma */
  var n := |nums|;
  var m :| CountOccurrences(nums, m) > n / 2;
  result := m;
  Majority_NoOtherGreater(nums, result);
}

// </vc-code>
