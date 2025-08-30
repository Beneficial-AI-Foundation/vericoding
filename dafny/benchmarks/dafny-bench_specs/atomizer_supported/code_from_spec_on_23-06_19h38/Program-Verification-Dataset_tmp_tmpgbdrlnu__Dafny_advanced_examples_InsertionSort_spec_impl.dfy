// ATOM 
predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
requires a!=null       
requires 0<=start<=end<=a.Length       
reads a       
{           
  forall j,k:: start<=j<k<end ==> a[j]<=a[k]
}

//IMPL InsertionSort
method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
{
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant sorted(a, 0, i)
    {
        var key := a[i];
        var j := i - 1;
        
        /* code modified by LLM (iteration 4): Updated invariants to better capture the shifting process */
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant sorted(a, 0, j+1)
            invariant forall k :: j+2 <= k <= i+1 ==> a[k] > key
            invariant j >= 0 ==> a[j] > key
            invariant forall k :: 0 <= k <= j ==> forall m :: j+2 <= m <= i+1 ==> a[k] <= a[m]
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        a[j + 1] := key;
        
        /* code modified by LLM (iteration 4): Added comprehensive assertions to establish sortedness after insertion */
        assert j == -1 || a[j] <= key;
        assert forall k :: j+2 <= k <= i+1 ==> a[k] >= key;
        assert a[j+1] == key;
        
        /* code modified by LLM (iteration 4): Key lemma to establish sortedness across the insertion point */
        assert forall x, y :: 0 <= x < j+1 && j+1 <= y <= i ==> a[x] <= a[y];
        assert forall x, y :: 0 <= x <= j && j+2 <= y <= i ==> a[x] <= a[y];
        assert sorted(a, 0, j+2);
        assert sorted(a, j+1, i+1);
        
        /* code modified by LLM (iteration 4): Final assertion to prove complete sortedness */
        assert sorted(a, 0, i+1);
        
        i := i + 1;
    }
}

//IMPL Main      
method Main(){
}