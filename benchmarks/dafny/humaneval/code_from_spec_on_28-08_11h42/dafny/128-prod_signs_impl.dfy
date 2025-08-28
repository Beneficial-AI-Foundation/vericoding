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
lemma sum_abs_preserves_sign(s: seq<int>, sign: int)
  requires sign == 1 || sign == -1
  ensures sign == 1 ==> sum_abs(s) * sign >= 0
  ensures sign == -1 ==> sum_abs(s) * sign <= 0
{
  if sign == 1 {
    assert sum_abs(s) >= 0;
  } else {
    assert sum_abs(s) >= 0;
    assert sum_abs(s) * (-1) <= 0;
  }
}

lemma count_negatives_mod_2(numbers: seq<int>)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 || |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1
{
}

lemma abs_product_equality(numbers: seq<int>, sign: int)
  requires sign == 1 || sign == -1
  ensures abs(sum_abs(numbers) * sign) == sum_abs(numbers)
{
  if sign == 1 {
    assert sum_abs(numbers) * 1 == sum_abs(numbers);
    assert sum_abs(numbers) >= 0;
    assert abs(sum_abs(numbers)) == sum_abs(numbers);
  } else {
    assert sum_abs(numbers) >= 0;
    assert sum_abs(numbers) * (-1) == -sum_abs(numbers);
    if sum_abs(numbers) == 0 {
      assert abs(0) == 0;
    } else {
      assert sum_abs(numbers) > 0;
      assert -sum_abs(numbers) < 0;
      assert abs(-sum_abs(numbers)) == sum_abs(numbers);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method prod_signs(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
// </vc-spec>
// <vc-code>
{
  var neg_count := |set i | 0 <= i < |numbers| && numbers[i] < 0|;
  var sign := if neg_count % 2 == 0 then 1 else -1;
  s := sum_abs(numbers) * sign;
  
  abs_product_equality(numbers, sign);
  
  if neg_count % 2 == 1 {
    assert sign == -1;
    assert s == sum_abs(numbers) * (-1);
    assert s <= 0;
  } else {
    assert sign == 1;
    assert s == sum_abs(numbers) * 1;
    assert s >= 0;
  }
}
// </vc-code>
