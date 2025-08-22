//IMPL TestLinearSearch

method LinearSearch(arr: array<int>, target: int) returns (index: int)
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures 0 <= index < arr.Length ==> arr[index] == target
{
  index := -1;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant index == -1 ==> forall j :: 0 <= j < i ==> arr[j] != target
    invariant 0 <= index < arr.Length ==> arr[index] == target
  {
    if arr[i] == target {
      index := i;
      return;
    }
    i := i + 1;
  }
}

method TestLinearSearch() {
  // Test case 1: Element found
  var arr1 := new int[5];
  arr1[0], arr1[1], arr1[2], arr1[3], arr1[4] := 1, 3, 5, 7, 9;
  var result1 := LinearSearch(arr1, 5);
  /* code modified by LLM (iteration 1): use postcondition directly and verify specific case */
  assert result1 == 2;
  
  // Test case 2: Element not found
  var arr2 := new int[3];
  arr2[0], arr2[1], arr2[2] := 2, 4, 6;
  var result2 := LinearSearch(arr2, 5);
  /* code modified by LLM (iteration 1): verify element not found case using postcondition */
  assert result2 == -1;
  assert forall i :: 0 <= i < arr2.Length ==> arr2[i] != 5;
  
  // Test case 3: Empty array
  var arr3 := new int[0];
  var result3 := LinearSearch(arr3, 1);
  /* code modified by LLM (iteration 1): verify empty array case */
  assert result3 == -1;
  
  // Test case 4: First element
  var arr4 := new int[4];
  arr4[0], arr4[1], arr4[2], arr4[3] := 10, 20, 30, 40;
  var result4 := LinearSearch(arr4, 10);
  /* code modified by LLM (iteration 1): verify that first element is found correctly */
  assert result4 == 0;
}