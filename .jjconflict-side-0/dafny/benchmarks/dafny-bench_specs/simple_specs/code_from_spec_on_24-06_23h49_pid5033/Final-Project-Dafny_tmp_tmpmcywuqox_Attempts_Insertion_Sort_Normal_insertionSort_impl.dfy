//ATOM

predicate sortedA (a: array<int>, i: int)

	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}


//ATOM

method lookForMin (a: array<int>, i: int) returns (m: int)

	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
  m := 0;
  assume i <= m < a.Length;
  assume forall k :: i <= k < a.Length ==> a[k] >= a[m];
  return m;
}


//ATOM
predicate sorted (a: array<int>)

	reads a
{
	sortedA(a, a.Length)
}


//IMPL insertionSort

method insertionSort (a: array<int>)

	modifies a
	ensures sorted(a)
{
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant sortedA(a, i)
    {
        var key := a[i];
        var j := i - 1;
        
        /* code modified by LLM (iteration 1): Simplified loop invariants for key insertion phase */
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant forall k :: j + 2 <= k <= i ==> a[k] > key
            invariant sortedA(a, j + 1)
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        /* code modified by LLM (iteration 1): Insert key at correct position */
        a[j + 1] := key;
        
        /* code modified by LLM (iteration 1): Assert sortedness after insertion to help verification */
        assert a[j + 1] == key;
        assert forall k :: j + 2 <= k <= i ==> a[k] >= key;
        assert j + 1 == 0 || a[j] <= key;
        assert sortedA(a, i + 1);
        
        i := i + 1;
    }
}