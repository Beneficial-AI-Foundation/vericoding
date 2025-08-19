predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

//ATOM
/* code modified by LLM (iteration 1): Implemented proper logic to find triple or return array length */
method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
  index := 0;
  while index < a.Length - 2
    invariant 0 <= index <= a.Length - 2
    invariant forall j :: 0 <= j < index ==> !(a[j] == a[j + 1] == a[j + 2])
  {
    if a[index] == a[index + 1] == a[index + 2] {
      return;
    }
    index := index + 1;
  }
  index := a.Length;
}

//IMPL TesterGetTriple
method TesterGetTriple()
{
  var a1 := new int[5];
  a1[0] := 1; a1[1] := 2; a1[2] := 2; a1[3] := 2; a1[4] := 3;
  var result1 := GetTriple(a1);
  
  var a2 := new int[4];
  a2[0] := 1; a2[1] := 2; a2[2] := 3; a2[3] := 4;
  var result2 := GetTriple(a2);
  
  var a3 := new int[0];
  var result3 := GetTriple(a3);
}