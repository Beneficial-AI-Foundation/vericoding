//IMPL
method ToArray<T>(xs: seq<T>) returns (a: array<T>)
ensures fresh(a)
ensures a.Length == |xs|
ensures forall i :: 0 <= i < |xs| ==> a[i] == xs[i]
{
    /* code modified by LLM (iteration 1): Added default value initialization for array creation */
    if |xs| == 0 {
        a := new T[0];
    } else {
        a := new T[|xs|](_ => xs[0]);
        var i := 0;
        while i < |xs|
            invariant 0 <= i <= |xs|
            invariant forall j :: 0 <= j < i ==> a[j] == xs[j]
        {
            a[i] := xs[i];
            i := i + 1;
        }
    }
}