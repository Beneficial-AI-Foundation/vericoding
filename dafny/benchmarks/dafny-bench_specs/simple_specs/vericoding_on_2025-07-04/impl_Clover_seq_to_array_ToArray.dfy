//IMPL
method ToArray<T>(xs: seq<T>) returns (a: array<T>)
ensures fresh(a)
ensures a.Length == |xs|
ensures forall i :: 0 <= i < |xs| ==> a[i] == xs[i]
{
    a := new T[|xs|];
    var i := 0;
    /* code modified by LLM (iteration 4): fixed while loop syntax by placing opening brace correctly */
    while i < |xs|
        invariant 0 <= i <= |xs|
        invariant forall j :: 0 <= j < i ==> a[j] == xs[j]
        invariant a.Length == |xs|
    {
        a[i] := xs[i];
        i := i + 1;
    }
}