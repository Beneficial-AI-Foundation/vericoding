

// <vc-helpers>
lemma digits_sum_preserves_sign(x: int)
  ensures x >= 0 ==> digits_sum(x) >= 0
  ensures x < 0 && abs(x) >= 10 ==> digits_sum(x) <= 0
  decreases abs(x)
{
  if abs(x) < 10 {
    // base case: digits_sum(x) == x
  } else {
    // recursive case: digits_sum(x) == x % 10 + digits_sum(x / 10)
    if x >= 0 {
      digits_sum_preserves_sign(x / 10);
    } else {
      digits_sum_preserves_sign(x / 10);
    }
  }
}

lemma set_cardinality_helper(s: seq<int>, i: nat)
  requires i <= |s|
  ensures |set j | 0 <= j < i && digits_sum(s[j]) > 0| <= i
{
  if i == 0 {
    assert set j | 0 <= j < i && digits_sum(s[j]) > 0 == {};
  } else {
    set_cardinality_helper(s, i - 1);
    var prev_set := set j | 0 <= j < i - 1 && digits_sum(s[j]) > 0;
    var curr_set := set j | 0 <= j < i && digits_sum(s[j]) > 0;
    if digits_sum(s[i-1]) > 0 {
      assert curr_set == prev_set + {i-1};
    } else {
      assert curr_set == prev_set;
    }
  }
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
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |set j | 0 <= j < i && digits_sum(s[j]) > 0|
  {
    digits_sum_preserves_sign(s[i]);
    
    if digits_sum(s[i]) > 0 {
      cnt := cnt + 1;
    }
    
    // Prove the invariant for i + 1
    var prev_set := set j | 0 <= j < i && digits_sum(s[j]) > 0;
    var next_set := set j | 0 <= j < i + 1 && digits_sum(s[j]) > 0;
    
    if digits_sum(s[i]) > 0 {
      assert next_set == prev_set + {i};
      assert i !in prev_set;
      assert |next_set| == |prev_set| + 1;
    } else {
      assert next_set == prev_set;
    }
    
    i := i + 1;
  }
  
  assert i == |s|;
  assert cnt == |set j | 0 <= j < |s| && digits_sum(s[j]) > 0|;
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