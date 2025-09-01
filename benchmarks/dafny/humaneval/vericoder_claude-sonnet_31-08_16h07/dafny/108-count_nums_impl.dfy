

// <vc-helpers>
lemma digits_sum_preserves_sign(x: int)
  ensures x >= 0 ==> digits_sum(x) >= 0
  ensures x < 0 ==> digits_sum(x) <= 0
  decreases abs(x)
{
  if abs(x) < 10 {
    // Base case: single digit
    if x < 0 {
      assert digits_sum(x) == x;
      assert x < 0 ==> digits_sum(x) <= 0;
    }
  } else {
    // Inductive case
    digits_sum_preserves_sign(x / 10);
    if x < 0 {
      assert x / 10 <= 0;
      assert digits_sum(x / 10) <= 0;
      assert x % 10 <= 0;
      assert digits_sum(x) == x % 10 + digits_sum(x / 10) <= 0;
    }
  }
}

lemma set_cardinality_bound(s: seq<int>)
  ensures |set i {:trigger} | 0 <= i < |s| && digits_sum(s[i]) > 0| <= |s|
{
  var target_set := set i {:trigger} | 0 <= i < |s| && digits_sum(s[i]) > 0;
  var index_set := set i {:trigger} | 0 <= i < |s|;
  assert target_set <= index_set;
  
  // Prove that index_set has the same cardinality as |s|
  assert forall i :: i in index_set <==> 0 <= i < |s|;
  if |s| == 0 {
    assert index_set == {};
    assert |index_set| == 0 == |s|;
  } else {
    // For non-empty sequences, the set of valid indices has cardinality |s|
    assert index_set == set i | 0 <= i < |s|;
    SetCardinalityLemma(s, 0);
  }
}

lemma SetCardinalityLemma(s: seq<int>, start: nat)
  requires start <= |s|
  ensures |set i | start <= i < |s|| == |s| - start
  decreases |s| - start
{
  if start == |s| {
    assert set i | start <= i < |s| == {};
  } else {
    var curr_set := set i | start <= i < |s|;
    var next_set := set i | start + 1 <= i < |s|;
    assert curr_set == {start} + next_set;
    assert start !in next_set;
    SetCardinalityLemma(s, start + 1);
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
  set_cardinality_bound(s);
  
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