method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
{
  /* code modified by LLM (iteration 1): Implemented proper search logic instead of using assume */
  x := 0;
  while x < a.Length
    invariant 0 <= x <= a.Length
    invariant forall i | 0 <= i < x :: a[i] != 'e'
  {
    if a[x] == 'e' {
      return x;
    }
    x := x + 1;
  }
  x := -1;
}

//IMPL 
method Main() {
	/* code modified by LLM (iteration 1): Fixed array initialization syntax - replaced new char[][] with proper new char[n] syntax */
	var a: array<char> := new char[6];
	a[0] := 'c'; a[1] := 'h'; a[2] := 'e'; a[3] := 'e'; a[4] := 's'; a[5] := 'e';
	var res := firstE(a);
	
	/* code modified by LLM (iteration 1): Fixed array initialization syntax for single element array */
	a := new char[1];
	a[0] := 'e';
	res := firstE(a);
	
	/* code modified by LLM (iteration 1): Fixed empty array initialization syntax */
	a := new char[0];
	res := firstE(a);
}