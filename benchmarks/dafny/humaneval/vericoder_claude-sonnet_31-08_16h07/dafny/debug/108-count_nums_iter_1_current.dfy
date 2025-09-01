

// <vc-helpers>
lemma digits_sum_preserves_sign(x: int)
  ensures x >= 0 ==> digits_sum(x) >= 0
  ensures x < 0 ==> digits_sum(x) <= 0
  decreases abs(x)
{
  if abs(x) < 10 {
    // Base case: single digit
  } else {
    // Inductive case
    digits_sum_preserves_sign(x / 10);
  }
}

lemma set_cardinality_bound(s: seq<int>)
  ensures |set i | 0 <= i < |s| && digits_sum(s[i]) > 0| <= |s|
{
  var target_set := set i | 0 <= i < |s| && digits_sum(s[i]) > 0;
  var index_set := set i | 0 <= i < |s|;
  assert target_set <= index_set;
  assert |index_set| == |s|;
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
  var processed := {};
  
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant processed == set j | 0 <= j < i && digits_sum(s[j]) > 0
    invariant cnt == |processed|
    invariant cnt <= i
  {
    digits_sum_preserves_sign(s[i]);
    
    if digits_sum(s[i]) > 0 {
      processed := processed + {i};
      cnt := cnt + 1;
    }
    
    assert processed == set j | 0 <= j < i + 1 && digits_sum(s[j]) > 0;
  }
  
  assert processed == set i | 0 <= i < |s| && digits_sum(s[i]) > 0;
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