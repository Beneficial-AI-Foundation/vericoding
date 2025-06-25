//ATOM

method BubbleSort(A:array<int>)
  modifies A
  ensures sorted(A)
  ensures multiset(A[..]) == multiset(old(A[..]))
{
  assume sorted(A);
  assume multiset(A[..]) == multiset(old(A[..]));
}


//ATOM

predicate sorted(A:array<int>)
  reads A
{
  sorted_between(A, 0, A.Length-1)
}


//ATOM

predicate sorted_between(A:array<int>, from:int, to:int)
  reads A
{
  forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}


//IMPL

method Main() {
  /* code modified by LLM (iteration 1): created array and initialized elements properly */
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
  /* code modified by LLM (iteration 1): call BubbleSort method */
  BubbleSort(A);
  /* code modified by LLM (iteration 1): print the sorted array */
  print A[..];
}

/* Explanation:

   // A is ordered for each pair of elements such that
   // the first element belongs to the left partition of i
   // and the second element belongs to the right partition of i

   // There is a variable defined by the value that the array takes at position j
   // Therefore, each value that the array takes for all elements from 0 to j
   // They are less than or equal to the value of the variable
*/