//ATOM
predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

//IMPL GetTriple
method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
    index := 0;
    /* code modified by LLM (iteration 4): fixed loop invariant and bounds checking */
    while index < a.Length - 2
        invariant 0 <= index <= a.Length - 2
        invariant forall j :: 0 <= j < index ==> !(a[j] == a[j + 1] == a[j + 2])
    {
        if a[index] == a[index + 1] == a[index + 2] {
            /* code modified by LLM (iteration 4): triple found, postconditions satisfied */
            assert triple(a);
            return;
        }
        index := index + 1;
    }
    /* code modified by LLM (iteration 4): loop terminated, no triple found */
    assert index == a.Length - 2;
    assert forall j :: 0 <= j < a.Length - 2 ==> !(a[j] == a[j + 1] == a[j + 2]);
    assert !triple(a);
    index := a.Length;
}