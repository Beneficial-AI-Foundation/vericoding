// <vc-helpers>
// Helper predicate to check if a number is even
predicate IsEven(n: int)
{
  n % 2 == 0
}

// Helper function to find the index of the smallest even value in the list
function FindSmallestEvenIndex(numbers: seq<int>): int
  requires |numbers| > 0
{
  var smallestEven := -1;
  var smallestIndex := -1;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant smallestIndex == -1 ==> smallestEven == -1
    invariant smallestIndex != -1 ==> 0 <= smallestIndex < i
    invariant smallestIndex != -1 ==> smallestEven == numbers[smallestIndex]
    invariant smallestIndex != -1 ==> IsEven(smallestEven)
    invariant forall k :: 0 <= k < i && IsEven(numbers[k]) ==> smallestEven == -1 || numbers[k] >= smallestEven
  {
    if IsEven(numbers[i]) {
      if smallestEven == -1 || numbers[i] < smallestEven {
        smallestEven := numbers[i];
        smallestIndex := i;
      }
    }
    i := i + 1;
  }
  smallestIndex
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def pluck(numbers: List[Int]) -> List[Int]
Given an array representing a branch of a tree that has non-negative integer nodes your task is to pluck one of the nodes and return it. The plucked node should be the node with the smallest even value. If multiple nodes with the same smallest even value are found return the node that has smallest index.
*/
// </vc-description>

// <vc-spec>
method Pluck(numbers: seq<int>) returns (result: seq<int>)
  requires |numbers| > 0
  ensures |result| == |numbers| - 1 || |result| == |numbers|
  ensures var idx := FindSmallestEvenIndex(numbers); 
          idx != -1 ==> result == numbers[..idx] + numbers[idx+1..]
  ensures var idx := FindSmallestEvenIndex(numbers); 
          idx == -1 ==> result == numbers
  ensures var idx := FindSmallestEvenIndex(numbers); 
          idx != -1 ==> IsEven(numbers[idx]) && 
                        forall k :: 0 <= k < |numbers| && IsEven(numbers[k]) ==> numbers[k] >= numbers[idx]
// </vc-spec>
// <vc-code>
{
  var idx := FindSmallestEvenIndex(numbers);
  if idx == -1 {
    result := numbers;
  } else {
    result := numbers[..idx] + numbers[idx+1..];
  }
}
// </vc-code>
