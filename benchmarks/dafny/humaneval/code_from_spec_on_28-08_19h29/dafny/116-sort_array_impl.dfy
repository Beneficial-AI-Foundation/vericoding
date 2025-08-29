function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
// Helper function to count the number of 1's in binary representation
function CountOnes(n: nat): nat {
  if n == 0 then 0
  else CountOnes(n / 2) + n % 2
}

// Helper lemma to ensure CountOnes behaves correctly
lemma CountOnesCorrect(n: nat)
  ensures CountOnes(n) >= 0
{
  if n == 0 {
    assert CountOnes(n) == 0;
  } else {
    CountOnesCorrect(n / 2);
    assert CountOnes(n) == CountOnes(n / 2) + n % 2;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def max_fill_count(grid : list[list[int]], capacity : int) -> int
Please write a function that sorts an array of non-negative integers according to number of ones in their binary representation in ascending order. For similar number of ones, sort based on decimal value.
*/
// </vc-description>

// <vc-spec>
method SortByBinaryOnes(arr: array<nat>) returns (sortedArr: array<nat>)
  requires arr.Length > 0
  ensures sortedArr.Length == arr.Length
  ensures forall i, j :: 0 <= i < j < sortedArr.Length ==> 
            (CountOnes(sortedArr[i]) < CountOnes(sortedArr[j]) || 
             (CountOnes(sortedArr[i]) == CountOnes(sortedArr[j]) && sortedArr[i] <= sortedArr[j]))
  ensures multiset(sortedArr[..]) == multiset(arr[..])
// </vc-spec>
// <vc-code>
{
  sortedArr := new nat[arr.Length];
  // Copy input array to sortedArr
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> sortedArr[k] == arr[k]
  {
    sortedArr[i] := arr[i];
  }
  
  // Bubble sort based on CountOnes and value
  var n := arr.Length;
  while n > 0
    invariant 0 <= n <= arr.Length
    invariant multiset(sortedArr[..]) == multiset(arr[..])
    invariant forall i, j :: 0 <= i < j < arr.Length - n ==> 
              (CountOnes(sortedArr[i]) < CountOnes(sortedArr[j]) || 
               (CountOnes(sortedArr[i]) == CountOnes(sortedArr[j]) && sortedArr[i] <= sortedArr[j]))
  {
    var newN := 0;
    for j := 0 to n - 1
      invariant 0 <= j <= n - 1
      invariant multiset(sortedArr[..]) == multiset(arr[..])
      invariant forall i, k :: 0 <= i < k < arr.Length - n ==> 
                (CountOnes(sortedArr[i]) < CountOnes(sortedArr[k]) || 
                 (CountOnes(sortedArr[i]) == CountOnes(sortedArr[k]) && sortedArr[i] <= sortedArr[k]))
      invariant 0 <= newN <= j + 1
      invariant forall k :: 0 <= k < newN ==> 
                (j > k ==> (CountOnes(sortedArr[k]) < CountOnes(sortedArr[k+1]) || 
                            (CountOnes(sortedArr[k]) == CountOnes(sortedArr[k+1]) && sortedArr[k] <= sortedArr[k+1])))
    {
      if j < n - 1 && (CountOnes(sortedArr[j]) > CountOnes(sortedArr[j+1]) || 
         (CountOnes(sortedArr[j]) == CountOnes(sortedArr[j+1]) && sortedArr[j] > sortedArr[j+1])) {
        var temp := sortedArr[j];
        sortedArr[j] := sortedArr[j+1];
        sortedArr[j+1] := temp;
        newN := j + 1;
      }
    }
    n := newN;
  }
}
// </vc-code>
