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
    /* code modified by LLM (iteration 1): handle case when array is too small for triples */
    if a.Length < 3 {
        index := a.Length;
        return;
    }
    
    index := 0;
    while index < a.Length - 2
        /* code modified by LLM (iteration 1): fixed invariant bounds to handle edge cases */
        invariant 0 <= index <= a.Length - 2
        invariant forall k :: 0 <= k < index ==> !(a[k] == a[k + 1] == a[k + 2])
    {
        if a[index] == a[index + 1] == a[index + 2] {
            return;
        }
        index := index + 1;
    }
    /* code modified by LLM (iteration 1): added assertion to help prove no triple exists */
    assert forall k :: 0 <= k < a.Length - 2 ==> !(a[k] == a[k + 1] == a[k + 2]);
    index := a.Length;
}

//IMPL TesterGetTriple
method TesterGetTriple()
{
    var a1 := new int[5];
    a1[0], a1[1], a1[2], a1[3], a1[4] := 1, 1, 1, 2, 3;
    var idx1 := GetTriple(a1);
    /* code modified by LLM (iteration 1): added assertion to help verify triple exists at index 0 */
    assert a1[0] == a1[1] == a1[2] == 1;
    assert idx1 == 0;
    
    var a2 := new int[4];
    a2[0], a2[1], a2[2], a2[3] := 1, 2, 1, 2;
    var idx2 := GetTriple(a2);
    /* code modified by LLM (iteration 1): added assertions to prove no triple exists */
    assert a2[0] != a2[1];
    assert a2[1] != a2[2];
    assert idx2 == 4;
    
    var a3 := new int[6];
    a3[0], a3[1], a3[2], a3[3], a3[4], a3[5] := 1, 2, 3, 3, 3, 4;
    var idx3 := GetTriple(a3);
    /* code modified by LLM (iteration 1): added assertions to help verify triple exists at index 2 */
    assert a3[0] != a3[1];
    assert a3[1] != a3[2];
    assert a3[2] == a3[3] == a3[4] == 3;
    assert idx3 == 2;
}