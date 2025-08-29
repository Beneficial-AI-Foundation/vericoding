function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
  ensures x >= 0 ==> abs(x) == x
  ensures x < 0 ==> abs(x) == -x
{
  if x >= 0 then x else -x
}
function sum_abs(s: seq<int>) : int
  ensures sum_abs(s) >= 0
{
  if |s| == 0 then 0 else abs(s[0]) + sum_abs(s[1..])
}

// <vc-helpers>
lemma sum_abs_distributive(s1: seq<int>, s2: seq<int>)
  ensures sum_abs(s1 + s2) == sum_abs(s1) + sum_abs(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    sum_abs_distributive(s1[1..], s2);
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
  }
}

function count_negatives(numbers: seq<int>): int
  ensures count_negatives(numbers) >= 0
{
  if |numbers| == 0 then 0
  else (if numbers[0] < 0 then 1 else 0) + count_negatives(numbers[1..])
}

lemma count_negatives_correct(numbers: seq<int>)
  ensures count_negatives(numbers) == |set i | 0 <= i < |numbers| && numbers[i] < 0|
{
  if |numbers| == 0 {
  } else {
    count_negatives_correct(numbers[1..]);
    var tail_set := set i | 0 <= i < |numbers[1..]| && numbers[1..][i] < 0;
    var full_set := set i | 0 <= i < |numbers| && numbers[i] < 0;
    var shifted_tail_set := set i | 1 <= i < |numbers| && numbers[i] < 0;
    
    forall i | i in tail_set ensures i + 1 in shifted_tail_set {
      assert numbers[1..][i] == numbers[i+1];
    }
    forall i | i in shifted_tail_set ensures i - 1 in tail_set {
      assert numbers[i] == numbers[1..][i-1];
    }
    assert tail_set == set i | 1 <= i < |numbers| && numbers[1..][i-1] < 0;
    assert tail_set == set j | j in set (i-1) | 1 <= i < |numbers| && numbers[i] < 0;
    
    if numbers[0] < 0 {
      assert full_set == {0} + shifted_tail_set;
      assert 0 !in shifted_tail_set;
    } else {
      assert full_set == shifted_tail_set;
    }
  }
}

function has_zero(numbers: seq<int>): bool
{
  exists i :: 0 <= i < |numbers| && numbers[i] == 0
}

lemma sum_abs_zero_property(numbers: seq<int>)
  requires has_zero(numbers)
  ensures sum_abs(numbers) >= 0
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def prod_signs(arr: List[int]) -> Optional[int]
You are given an array arr of integers and you need to return sum of magnitudes of integers multiplied by product of all signs of each number in the array, represented by 1, -1 or 0. Note: return None for empty arr.
*/
// </vc-description>

// <vc-spec>
method prod_signs(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
// </vc-spec>

// <vc-code>
{
  if |numbers| == 0 {
    s := 0;
    return;
  }
  
  var sum_magnitudes := sum_abs(numbers);
  var neg_count := count_negatives(numbers);
  var contains_zero := has_zero(numbers);
  
  count_negatives_correct(numbers);
  
  if contains_zero {
    s := 0;
  } else if neg_count % 2 == 1 {
    s := -sum_magnitudes;
  } else {
    s := sum_magnitudes;
  }
}
// </vc-code>

