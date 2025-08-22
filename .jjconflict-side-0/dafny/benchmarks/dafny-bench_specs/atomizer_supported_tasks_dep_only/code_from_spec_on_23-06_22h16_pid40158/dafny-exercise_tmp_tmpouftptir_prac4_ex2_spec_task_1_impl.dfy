// ATOM 
predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

// IMPL 
method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
    if a.Length < 3 {
        return a.Length;
    }
    
    var i := 0;
    while i < a.Length - 2
        invariant 0 <= i <= a.Length - 2
        invariant forall j :: 0 <= j < i ==> !(a[j] == a[j + 1] == a[j + 2])
    {
        if a[i] == a[i + 1] == a[i + 2] {
            return i;
        }
        i := i + 1;
    }
    
    return a.Length;
}

//ATOM_PLACEHOLDER_TesterGetTriple