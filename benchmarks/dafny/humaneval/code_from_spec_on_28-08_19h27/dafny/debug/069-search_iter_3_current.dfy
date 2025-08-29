// <vc-helpers>
function count(numbers: seq<int>, value: int): int
{
  |set i | 0 <= i < |numbers| && numbers[i] == value|
}

lemma CountBounds(numbers: seq<int>, value: int)
  ensures 0 <= count(numbers, value) <= |numbers|
{
  var indices := set i | 0 <= i < |numbers| && numbers[i] == value;
  var allIndices := set i | 0 <= i < |numbers|;
  assert indices <= allIndices;
  assert |indices| <= |allIndices|;
  assert |allIndices| == |numbers|;
}

lemma CountCorrect(numbers: seq<int>, value: int)
  ensures count(numbers, value) == |set i | 0 <= i < |numbers| && numbers[i] == value|
{
}

lemma CountStable(numbers: seq<int>, value: int, i: int)
  requires 0 <= i <= |numbers|
  ensures count(numbers[..i], value) <= count(numbers, value)
{
  var prefixIndices := set j | 0 <= j < i && numbers[j] == value;
  var allIndices := set j | 0 <= j < |numbers| && numbers[j] == value;
  assert prefixIndices <= allIndices;
}

lemma CountMonotonic(numbers: seq<int>, value: int, i: int, j: int)
  requires 0 <= i <= j <= |numbers|
  ensures count(numbers[..i], value) <= count(numbers[..j], value)
{
  var iIndices := set k | 0 <= k < i && numbers[k] == value;
  var jIndices := set k | 0 <= k < j && numbers[k] == value;
  assert iIndices <= jIndices;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def search(numbers: List[int]) -> int
You are given a non-empty list of positive integers. Return the greatest integer that is greater than zero, and has a frequency greater than or equal to the value of the integer itself. The frequency of an integer is the number of times it appears in the list. If no such a value exist, return -1.
*/
// </vc-description>

// <vc-spec>
method search(numbers: seq<int>) returns (result: int)
  requires |numbers| > 0
  requires forall x :: x in numbers ==> x > 0
  ensures result == -1 || (result > 0 && count(numbers, result) >= result)
  ensures result != -1 ==> forall x :: x in numbers && x > result ==> count(numbers, x) < x
// </vc-spec>
// <vc-code>
{
  var maxValid := -1;
  var i := 0;
  
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant maxValid == -1 || (maxValid > 0 && count(numbers, maxValid) >= maxValid)
    invariant maxValid != -1 ==> forall x :: x in numbers[..i] && x > maxValid ==> count(numbers, x) < x
    invariant maxValid != -1 ==> maxValid in numbers[..i]
  {
    var current := numbers[i];
    var freq := count(numbers, current);
    
    if freq >= current && current > maxValid {
      maxValid := current;
    }
    
    i := i + 1;
  }
  
  // Final verification that maxValid satisfies the postcondition
  if maxValid != -1 {
    assert forall x :: x in numbers && x > maxValid ==> count(numbers, x) < x;
  }
  
  result := maxValid;
}
// </vc-code>
