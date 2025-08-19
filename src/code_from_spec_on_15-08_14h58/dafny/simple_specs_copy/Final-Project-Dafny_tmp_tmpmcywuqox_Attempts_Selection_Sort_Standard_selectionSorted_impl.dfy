//IMPL
method selectionSorted(Array: array<int>) 
 modifies Array
 ensures multiset(old(Array[..])) == multiset(Array[..])
{
    var n := Array.Length;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant multiset(old(Array[..])) == multiset(Array[..])
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < n
            invariant i <= minIndex < n
            invariant i + 1 <= j <= n
            invariant forall k :: i <= k < j ==> Array[minIndex] <= Array[k]
            invariant multiset(old(Array[..])) == multiset(Array[..])
        {
            if Array[j] < Array[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        if minIndex != i {
            var temp := Array[i];
            Array[i] := Array[minIndex];
            Array[minIndex] := temp;
        }
        
        i := i + 1;
    }
}