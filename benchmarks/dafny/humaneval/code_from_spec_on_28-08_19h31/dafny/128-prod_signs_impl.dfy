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
lemma SumAbsNonNegative(s: seq<int>)
  ensures sum_abs(s) >= 0
{
  if |s| == 0 {
    assert sum_abs(s) == 0;
  } else {
    assert sum_abs(s) == abs(s[0]) + sum_abs(s[1..]);
    SumAbsNonNegative(s[1..]);
    assert abs(s[0]) >= 0;
    assert sum_abs(s[1..]) >= 0;
  }
}

lemma AbsProductProperty(numbers: seq<int>, i: int)
  requires 0 <= i <= |numbers|
  ensures abs(product_signs(numbers[..i])) == sum_abs(numbers[..i])
{
  if i == 0 {
    assert numbers[..i] == [];
    assert product_signs([]) == 1;
    assert sum_abs([]) == 0;
    assert abs(1) == 1;
  } else {
    AbsProductProperty(numbers, i-1);
    var prev_product := product_signs(numbers[..i-1]);
    var curr_num := numbers[i-1];
    assert sum_abs(numbers[..i]) == sum_abs(numbers[..i-1]) + abs(curr_num);
    if curr_num < 0 {
      assert product_signs(numbers[..i]) == prev_product * (-abs(curr_num));
      calc {
        abs(product_signs(numbers[..i]));
        abs(prev_product * (-abs(curr_num)));
        abs(prev_product) * abs(-abs(curr_num));
        abs(prev_product) * abs(curr_num);
        sum_abs(numbers[..i-1]) * abs(curr_num);
      }
    } else {
      assert product_signs(numbers[..i]) == prev_product * abs(curr_num);
      calc {
        abs(product_signs(numbers[..i]));
        abs(prev_product * abs(curr_num));
        abs(prev_product) * abs(curr_num);
        sum_abs(numbers[..i-1]) * abs(curr_num);
      }
    }
    assert abs(product_signs(numbers[..i])) == sum_abs(numbers[..i-1]) * abs(curr_num);
    assert abs(product_signs(numbers[..i])) == sum_abs(numbers[..i]);
  }
}

lemma ProductSignsSign(numbers: seq<int>, i: int)
  requires 0 <= i <= |numbers|
  ensures product_signs(numbers[..i]) < 0 ==> |set k | 0 <= k < i && numbers[k] < 0| % 2 == 1
  ensures product_signs(numbers[..i]) > 0 ==> |set k | 0 <= k < i && numbers[k] < 0| % 2 == 0
{
  if i == 0 {
    assert product_signs(numbers[..i]) == 1;
    assert |set k | 0 <= k < i && numbers[k] < 0| == 0;
  } else {
    ProductSignsSign(numbers, i-1);
    var prev_neg_count := |set k | 0 <= k < i-1 && numbers[k] < 0|;
    var curr_num := numbers[i-1];
    if curr_num < 0 {
      var new_neg_count := prev_neg_count + 1;
      assert |set k | 0 <= k < i && numbers[k] < 0| == new_neg_count;
      if product_signs(numbers[..i-1]) < 0 {
        assert product_signs(numbers[..i]) > 0;
        assert prev_neg_count % 2 == 1;
        assert new_neg_count % 2 == 0;
      } else {
        assert product_signs(numbers[..i]) < 0;
        assert prev_neg_count % 2 == 0;
        assert new_neg_count % 2 == 1;
      }
    } else {
      assert |set k | 0 <= k < i && numbers[k] < 0| == prev_neg_count;
      if product_signs(numbers[..i-1]) < 0 {
        assert product_signs(numbers[..i]) < 0;
        assert prev_neg_count % 2 == 1;
      } else {
        assert product_signs(numbers[..i]) > 0;
        assert prev_neg_count % 2 == 0;
      }
    }
  }
}

function product_signs(numbers: seq<int>): int
{
  if |numbers| == 0 then 1
  else if numbers[0] < 0 then -abs(numbers[0]) * product_signs(numbers[1..])
  else abs(numbers[0]) * product_signs(numbers[1..])
}
// </vc-helpers>

// <vc-spec>
method prod_signs(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
// </vc-spec>
// <vc-code>
method ComputeProdSigns(numbers: seq<int>) returns (s: int)
  ensures abs(s) == sum_abs(numbers)
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 1 ==> s <= 0
  ensures |set i | 0 <= i < |numbers| && numbers[i] < 0| % 2 == 0 ==> s >= 0
{
  var result := 1;
  var i := 0;
  var neg_count := 0;
  
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant result == product_signs(numbers[..i])
    invariant neg_count == |set k | 0 <= k < i && numbers[k] < 0|
  {
    var curr_num := numbers[i];
    if curr_num < 0 {
      result := result * (-abs(curr_num));
      neg_count := neg_count + 1;
    } else {
      result := result * abs(curr_num);
    }
    i := i + 1;
  }
  
  s := result;
  AbsProductProperty(numbers, |numbers|);
  assert abs(s) == sum_abs(numbers);
  ProductSignsSign(numbers, |numbers|);
  if neg_count % 2 == 1 {
    assert s <= 0;
  } else {
    assert s >= 0;
  }
}
// </vc-code>
