//ATOM

method DivMod(a: int, b: int) returns (q: int, r: int)
{
  q := 0;
  r := 0;
  return q, r;
}

/*
  triple Hoare (| P |) S (| Q |) 
*/

//ATOM

// Exemplu de program

method SqrSum(n: int) returns (s: int)
{
  s := 0;
  return s;
}


// SPEC

method Main()
{
	var v := SqrSum(5);
	print "SqrSum(5): ", v, "\n";

	var q, r := DivMod(5, 3);
	print "DivMod(5, 3): ", q, ", ", r, "\n";

}