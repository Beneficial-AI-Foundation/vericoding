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
/* helper modified by LLM (iteration 4): bound counts of two distinct values sum to at most length */
lemma CountTwoValuesBound(nums: seq<int>, a: int, b: int)
  requires a != b
  ensures CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|
  decreases |nums|
{
  if |nums| == 0 {
  } else {
    var first := nums[0];
    CountTwoValuesBound(nums[1..], a, b);
    if first == a {
      assert CountOccurrences(nums, a) == CountOccurrences(nums[1..], a) + 1;
      assert first != b;
      assert CountOccurrences(nums, b) == CountOccurrences(nums[1..], b);
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b)
             == CountOccurrences(nums[1..], a) + CountOccurrences(nums[1..], b) + 1;
      assert CountOccurrences(nums[1..], a) + CountOccurrences(nums[1..], b) <= |nums[1..]|;
      assert |nums| == |nums[1..]| + 1;
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|;
    } else if first == b {
      assert CountOccurrences(nums, b) == CountOccurrences(nums[1..], b) + 1;
      assert first != a;
      assert CountOccurrences(nums, a) == CountOccurrences(nums[1..], a);
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b)
             == CountOccurrences(nums[1..], a) + CountOccurrences(nums[1..], b) + 1;
      assert CountOccurrences(nums[1..], a) + CountOccurrences(nums[1..], b) <= |nums[1..]|;
      assert |nums| == |nums[1..]| + 1;
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|;
    } else {
      assert CountOccurrences(nums, a) == CountOccurrences(nums[1..], a);
      assert CountOccurrences(nums, b) == CountOccurrences(nums[1..], b);
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b)
             == CountOccurrences(nums[1..], a) + CountOccurrences(nums[1..], b);
      assert CountOccurrences(nums[1..], a) + CountOccurrences(nums[1..], b) <= |nums[1..]|;
      assert |nums[1..]| <= |nums|;
      assert CountOccurrences(nums, a) + CountOccurrences(nums, b) <= |nums|;
    }
  }
}

/* helper modified by LLM (iteration 4): arithmetic fact n - (n/2 + 1) <= n/2 for n >= 0 */
lemma MinusHalfPlusOneLeHalf(n: int)
  requires n >= 0
  ensures n - (n/2 + 1) <= n/2
{
  var m := n / 2;
  if n % 2 == 0 {
    assert n == 2 * m;
    assert n - (m + 1) == m - 1;
    assert m - 1 <= m;
  } else {
    assert n == 2 * m + 1;
    assert n - (m + 1) == m;
  }
}

/* helper modified by LLM (iteration 4): show a > b implies a >= b + 1 for integers */
lemma IntGtImpliesGePlusOne(a: int, b: int)
  requires a > b
  ensures a >= b + 1
{
  assert a >= b + 1;
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
  /* code modified by LLM (iteration 4): implement majority element without assumptions, using counting lemmas */
  var w :| CountOccurrences(nums, w) > |nums| / 2;
  result := w;

  assert CountOccurrences(nums, result) > |nums| / 2;

  assert forall x :: x != result ==> CountOccurrences(nums, x) <= |nums| / 2
    by {
      forall x | x != result
        ensures CountOccurrences(nums, x) <= |nums| / 2
      {
        CountTwoValuesBound(nums, result, x);
        assert CountOccurrences(nums, result) + CountOccurrences(nums, x) <= |nums|;
        assert CountOccurrences(nums, x) <= |nums| - CountOccurrences(nums, result);
        IntGtImpliesGePlusOne(CountOccurrences(nums, result), |nums| / 2);
        assert |nums| - CountOccurrences(nums, result) <= |nums| - (|nums| / 2 + 1);
        MinusHalfPlusOneLeHalf(|nums|);
        assert |nums| - (|nums| / 2 + 1) <= |nums| / 2;
      }
    }
}
// </vc-code>
