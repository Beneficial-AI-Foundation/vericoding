// ATOM 
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
    if a.Length < 3 {
        /* code modified by LLM (iteration 2): added assertion to establish !triple(a) when length < 3 */
        assert !triple(a);
        index := a.Length;
        return;
    }
    
    index := 0;
    while index < a.Length - 2
        invariant 0 <= index <= a.Length - 2
        /* code modified by LLM (iteration 2): simplified invariant to track indices checked so far */
        invariant forall k :: 0 <= k < index ==> !(a[k] == a[k + 1] == a[k + 2])
    {
        if a[index] == a[index + 1] == a[index + 2] {
            /* code modified by LLM (iteration 2): added assertion to establish triple(a) when found */
            assert triple(a);
            return;
        }
        index := index + 1;
    }
    
    /* code modified by LLM (iteration 2): added assertion to prove !triple(a) when loop completes */
    assert forall k :: 0 <= k < a.Length - 2 ==> !(a[k] == a[k + 1] == a[k + 2]);
    assert !triple(a);
    index := a.Length;
}

//IMPL TesterGetTriple
method TesterGetTriple()
{
    var a1 := new int[5];
    a1[0] := 1; a1[1] := 1; a1[2] := 1; a1[3] := 2; a1[4] := 3;
    /* code modified by LLM (iteration 2): added assertion to establish triple(a1) before calling GetTriple */
    assert a1[0] == a1[1] == a1[2];
    assert triple(a1);
    var result1 := GetTriple(a1);
    assert result1 == 0;
    
    var a2 := new int[4];
    a2[0] := 1; a2[1] := 2; a2[2] := 1; a2[3] := 2;
    /* code modified by LLM (iteration 2): added assertions to establish !triple(a2) */
    assert !(a2[0] == a2[1] == a2[2]);
    assert !(a2[1] == a2[2] == a2[3]);
    assert !triple(a2);
    var result2 := GetTriple(a2);
    assert result2 == 4;
    
    var a3 := new int[2];
    a3[0] := 1; a3[1] := 1;
    /* code modified by LLM (iteration 2): added assertion to establish !triple(a3) due to length < 3 */
    assert !triple(a3);
    var result3 := GetTriple(a3);
    assert result3 == 2;
}