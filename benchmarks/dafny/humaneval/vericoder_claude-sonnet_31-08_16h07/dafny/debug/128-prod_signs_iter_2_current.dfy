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

lemma negative_count_invariant(numbers: seq<int>, i: int)
  requires 0 <= i <= |numbers|
  ensures |set j | 0 <= j < i && numbers[j] < 0| == |set j | 0 <= j < |numbers[..i]| && numbers[..i][j] < 0|
{
  var s1 := set j | 0 <= j < i && numbers[j] < 0;
  var s2 := set j | 0 <= j < |numbers[..i]| && numbers[..i][j] < 0;
  
  assert |numbers[..i]| == i;
  
  // Show s1 ⊆ s2
  forall j | j in s1
    ensures j in s2
  {
    assert 0 <= j < i && numbers[j] < 0;
    assert 0 <= j < |numbers[..i]|;
    assert numbers[..i][j] == numbers[j];
    assert numbers[..i][j] < 0;
  }
  
  // Show s2 ⊆ s1
  forall j | j in s2
    ensures j in s1
  {
    assert 0 <= j < |numbers[..i]| && numbers[..i][j] < 0;
    assert 0 <= j < i;
    assert numbers[j] == numbers[..i][j];
    assert numbers[j] < 0;
  }
  
  assert s1 == s2;
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
      neg_count := neg_count + 1;
    }
    i := i + 1;
    negative_count_invariant(numbers, i);
  }
  
  var sum_of_abs := sum_abs(numbers);
  
  if neg_count % 2 == 0 {
    s := sum_of_abs;
  } else {
    s := -sum_of_abs;
  }
}
// </vc-code>

