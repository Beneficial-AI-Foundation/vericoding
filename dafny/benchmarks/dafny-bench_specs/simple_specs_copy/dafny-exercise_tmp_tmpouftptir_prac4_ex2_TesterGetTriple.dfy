//ATOM
predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}


//ATOM

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
  index := 0;
  assume 0 <= index < a.Length - 2 || index ==> a.Length;
  assume index ==> a.Length <==> !triple(a);
  assume 0 <= index < a.Length - 2 <==> triple(a);
  assume 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2];
  return index;
}


// SPEC

method TesterGetTriple()
{
}
