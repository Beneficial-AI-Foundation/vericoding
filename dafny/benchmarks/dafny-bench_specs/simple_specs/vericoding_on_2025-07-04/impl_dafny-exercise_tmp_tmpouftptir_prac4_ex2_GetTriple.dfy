//ATOM
predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

//IMPL 
method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
    /* code modified by LLM (iteration 4): Handle edge case when array is too small */
    if a.Length < 3 {
        index := a.Length;
        assert !triple(a);
        return;
    }
    
    index := 0;
    /* code modified by LLM (iteration 4): Fixed loop invariant to allow proper termination and bounds */
    while index < a.Length - 2
        invariant 0 <= index <= a.Length - 2
        invariant forall j :: 0 <= j < index ==> !(a[j] == a[j + 1] == a[j + 2])
    {
        if a[index] == a[index + 1] == a[index + 2] {
            /* code modified by LLM (iteration 4): Added witness assertion to prove triple exists */
            assert a[index] == a[index + 1] == a[index + 2];
            assert triple(a) by {
                assert 0 <= index < a.Length - 2 && a[index] == a[index + 1] == a[index + 2];
            }
            return;
        }
        index := index + 1;
    }
    /* code modified by LLM (iteration 4): Added comprehensive proof that no triple exists */
    assert index == a.Length - 2;
    assert forall j :: 0 <= j < a.Length - 2 ==> !(a[j] == a[j + 1] == a[j + 2]);
    assert !triple(a) by {
        if triple(a) {
            var k :| 0 <= k < a.Length - 2 && a[k] == a[k + 1] == a[k + 2];
            assert !(a[k] == a[k + 1] == a[k + 2]);
            assert false;
        }
    }
    index := a.Length;
}