//IMPL BubbleSort
method BubbleSort(a: array?<int>)
 modifies a
 requires a != null
{
    var n := a.Length;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        var j := 0;
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
        {
            if a[j] > a[j + 1] {
                var temp := a[j];
                a[j] := a[j + 1];
                a[j + 1] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}