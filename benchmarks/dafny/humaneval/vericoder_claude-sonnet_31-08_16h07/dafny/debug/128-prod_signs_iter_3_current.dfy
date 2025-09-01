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
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    sum_abs_distributive(s1[1..], s2);
  }
}

lemma negative_count_step(numbers: seq<int>, i: int)
  requires 0 <= i < |numbers|
  ensures |set j | 0 <= j < i+1 && numbers[j] < 0| == 
          |set j | 0 <= j < i && numbers[j] < 0| + (if numbers[i] < 0 then 1 else 0)
{
  var old_set := set j | 0 <= j < i && numbers[j] < 0;
  var new_set := set j | 0 <= j < i+1 && numbers[j] < 0;
  
  if numbers[i] < 0 {
    assert new_set == old_set + {i};
    assert i !in old_set;
  } else {
    assert new_set == old_set;
  }
}

lemma sum_abs_prefix(numbers: seq<int>, i: int)
  requires 0 <= i <= |numbers|
  ensures sum_abs(numbers[..i]) + sum_abs(numbers[i..]) == sum_abs(numbers)
{
  if i == 0 {
    assert numbers[..0] == [];
    assert numbers[0..] == numbers;
  } else if i == |numbers| {
    assert numbers[..|numbers|] == numbers;
    assert numbers[|numbers|..] == [];
  } else {
    sum_abs_distributive(numbers[..i], numbers[i..]);
    assert numbers[..i] + numbers[i..] == numbers;
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
  if |numbers| == 0 {
    s := 0;
    return;
  }
  
  var neg_count := 0;
  var i := 0;
  
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant neg_count == |set j | 0 <= j < i && numbers[j] < 0|
  {
    if numbers[i] < 0 {
      negative_count_step(numbers, i);
      neg_count := neg_count + 1;
    } else {
      negative_count_step(numbers, i);
    }
    i := i + 1;
  }
  
  var sum_of_abs := sum_abs(numbers);
  
  if neg_count % 2 == 0 {
    s := sum_of_abs;
  } else {
    s := -sum_of_abs;
  }
}
// </vc-code>

