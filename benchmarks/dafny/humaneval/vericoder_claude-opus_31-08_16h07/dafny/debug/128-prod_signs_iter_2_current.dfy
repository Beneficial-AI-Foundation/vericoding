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
lemma sum_abs_append(s1: seq<int>, s2: seq<int>)
  ensures sum_abs(s1 + s2) == sum_abs(s1) + sum_abs(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    sum_abs_append(s1[1..], s2);
  }
}

lemma set_card_add(s: set<int>, x: int)
  requires x !in s
  ensures |s + {x}| == |s| + 1
{
}

lemma set_card_same(s: set<int>, x: int)
  requires x in s
  ensures |s + {x}| == |s|
{
  assert s + {x} == s;
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
  var sum := 0;
  var negative_count := 0;
  var seen_negatives: set<int> := {};
  
  for i := 0 to |numbers|
    invariant 0 <= i <= |numbers|
    invariant sum == sum_abs(numbers[..i])
    invariant seen_negatives == set j | 0 <= j < i && numbers[j] < 0
    invariant negative_count == |seen_negatives|
  {
    sum := sum + abs(numbers[i]);
    
    assert numbers[..i+1] == numbers[..i] + [numbers[i]];
    sum_abs_append(numbers[..i], [numbers[i]]);
    assert sum_abs(numbers[..i+1]) == sum_abs(numbers[..i]) + sum_abs([numbers[i]]);
    assert sum_abs([numbers[i]]) == abs(numbers[i]);
    
    if numbers[i] < 0 {
      var old_size := |seen_negatives|;
      seen_negatives := seen_negatives + {i};
      
      if i in (set j | 0 <= j < i && numbers[j] < 0) {
        set_card_same((set j | 0 <= j < i && numbers[j] < 0), i);
      } else {
        set_card_add((set j | 0 <= j < i && numbers[j] < 0), i);
        negative_count := negative_count + 1;
      }
    }
    
    assert seen_negatives == set j | 0 <= j < i+1 && numbers[j] < 0;
  }
  
  assert numbers[..|numbers|] == numbers;
  assert sum == sum_abs(numbers);
  assert seen_negatives == set j | 0 <= j < |numbers| && numbers[j] < 0;
  
  if negative_count % 2 == 1 {
    s := -sum;
  } else {
    s := sum;
  }
}
// </vc-code>

