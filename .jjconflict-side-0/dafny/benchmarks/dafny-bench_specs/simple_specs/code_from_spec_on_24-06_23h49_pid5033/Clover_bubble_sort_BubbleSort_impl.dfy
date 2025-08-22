//IMPL 
method BubbleSort(a: array<int>)
 modifies a
 ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
 ensures multiset(a[..])==multiset(old(a[..]))
{
    var n := a.Length;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        /* code modified by LLM (iteration 4): The last i elements are sorted and are the largest elements */
        invariant forall x, y :: n - i <= x < y < n ==> a[x] <= a[y]
        invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> a[x] <= a[y]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := 0;
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            /* code modified by LLM (iteration 4): Track that elements from j+1 onwards contain the maximum of elements 0..j+1 */
            invariant forall k :: j < k < n - i ==> forall m :: 0 <= m <= j ==> a[m] <= a[k]
            /* code modified by LLM (iteration 4): Maintain sorted suffix property */
            invariant forall x, y :: n - i <= x < y < n ==> a[x] <= a[y]
            /* code modified by LLM (iteration 4): Maintain partition property between unsorted and sorted parts */
            invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> a[x] <= a[y]
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            if a[j] > a[j + 1] {
                /* code modified by LLM (iteration 4): Swap elements */
                var temp := a[j];
                a[j] := a[j + 1];
                a[j + 1] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}