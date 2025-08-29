// <vc-helpers>
lemma digits_sum_properties(x: int)
  ensures x >= 0 ==> digits_sum(x) >= 0
  ensures x < 0 ==> digits_sum(x) <= 0
  decreases abs(x)
{
  if abs(x) < 10 {
    if x < 0 {
      assert digits_sum(x) == x;
      assert x < 0 ==> digits_sum(x) <= 0;
    }
  } else {
    digits_sum_properties(x / 10);
    if x < 0 {
      assert x % 10 <= 0;
      assert digits_sum(x / 10) <= 0;
      assert digits_sum(x) == x % 10 + digits_sum(x / 10) <= 0;
    }
  }
}

lemma set_cardinality_bound<T>(s: set<T>, n: int)
  requires forall x :: x in s ==> 0 <= x < n
  ensures |s| <= n
{
  if n <= 0 {
    assert s == {};
  } else {
    var s' := set x | x in s && x < n - 1;
    if (n - 1) in s {
      set_cardinality_bound(s', n - 1);
      assert s == s' + {n - 1};
      assert |s| == |s'| + 1 <= (n - 1) + 1 == n;
    } else {
      assert s == s';
      set_cardinality_bound(s', n - 1);
      assert |s| <= n - 1 < n;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def count_nums(arr: List[int]) -> int
Write a function count_nums which takes an array of integers and returns the number of elements which has a sum of digits > 0. If a number is negative, then its first signed digit will be negative: e.g. -123 has signed digits -1, 2, and 3.
*/
// </vc-description>

// <vc-spec>
method count_nums(arr: seq<int>) returns (count: int)
  ensures count >= 0
  ensures count <= |arr|
  ensures count == |set i | 0 <= i < |arr| && digits_sum(arr[i]) > 0|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant count >= 0
    invariant count == |set j | 0 <= j < i && digits_sum(arr[j]) > 0|
    invariant count <= i
  {
    digits_sum_properties(arr[i]);
    if digits_sum(arr[i]) > 0 {
      count := count + 1;
    }
    i := i + 1;
  }
  
  var positive_indices := set i | 0 <= i < |arr| && digits_sum(arr[i]) > 0;
  set_cardinality_bound(positive_indices, |arr|);
}
// </vc-code>

function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}
// pure-end
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}
// pure-end