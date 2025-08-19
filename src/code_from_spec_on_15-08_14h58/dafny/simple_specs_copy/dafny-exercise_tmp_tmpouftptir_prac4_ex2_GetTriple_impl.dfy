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
    /* code modified by LLM (iteration 1): added check for arrays too short to contain triples */
    if a.Length < 3 {
        index := a.Length;
        return;
    }
    
    index := 0;
    while index < a.Length - 2
        /* code modified by LLM (iteration 1): fixed invariant bounds to handle short arrays */
        invariant 0 <= index <= a.Length - 2
        invariant a.Length >= 3
        invariant forall j :: 0 <= j < index ==> !(a[j] == a[j + 1] == a[j + 2])
    {
        if a[index] == a[index + 1] == a[index + 2] {
            return;
        }
        index := index + 1;
    }
    index := a.Length;
}