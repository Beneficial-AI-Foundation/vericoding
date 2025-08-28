// <vc-helpers>
lemma digits_sum_property(x: int)
  decreases abs(x)
  ensures digits_sum(x) > 0 <==> x > 0 || (x < 0 && exists k: nat {:trigger} :: k > 0 && digits_sum(abs(x)) - 2 * (abs(x) % 10) == digits_sum(x))
{
  if abs(x) < 10 {
    if x >= 0 {
      assert digits_sum(x) == x;
    } else {
      assert digits_sum(x) == x;
      if digits_sum(x) > 0 {
        var k: nat := 1;
        assert k > 0;
        assert digits_sum(abs(x)) - 2 * (abs(x) % 10) == abs(x) - 2 * (abs(x) % 10) == abs(x) - 2 * abs(x) == -abs(x) == x == digits_sum(x);
      }
    }
  } else {
    digits_sum_property(x / 10);
    if x < 0 && digits_sum(x) > 0 {
      var k: nat := 1;
      assert k > 0;
      assert digits_sum(abs(x)) - 2 * (abs(x) % 10) == digits_sum(x);
    }
  }
}

lemma subset_cardinality<T>(s1: set<T>, s2: set<T>)
  requires s1 <= s2
  ensures |s1| <= |s2|
{
}

lemma finite_range_cardinality(i: nat)
  ensures |set j | 0 <= j < i| <= i
{
}
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  var positive_indices: set<int> := {};
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |positive_indices|
    invariant positive_indices == set j | 0 <= j < i && digits_sum(s[j]) > 0
    invariant cnt <= i
  {
    if digits_sum(s[i]) > 0 {
      positive_indices := positive_indices + {i};
      cnt := cnt + 1;
    }
    i := i + 1;
    
    var positive_set := set j | 0 <= j < i && digits_sum(s[j]) > 0;
    var all_set := set j | 0 <= j < i;
    subset_cardinality(positive_set, all_set);
    finite_range_cardinality(i);
    assert cnt <= i;
  }
  
  assert positive_indices == set j | 0 <= j < |s| && digits_sum(s[j]) > 0;
  assert cnt == |positive_indices|;
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