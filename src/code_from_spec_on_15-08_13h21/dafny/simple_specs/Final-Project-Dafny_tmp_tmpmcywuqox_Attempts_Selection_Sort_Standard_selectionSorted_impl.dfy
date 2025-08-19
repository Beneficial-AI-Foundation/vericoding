//IMPL 
method selectionSorted(Array: array<int>) 
 modifies Array
 ensures multiset(old(Array[..])) == multiset(Array[..])
{
    if Array.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < Array.Length - 1
        invariant 0 <= i <= Array.Length
        invariant multiset(old(Array[..])) == multiset(Array[..])
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < Array.Length
            invariant i < j <= Array.Length
            invariant i <= minIndex < Array.Length
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