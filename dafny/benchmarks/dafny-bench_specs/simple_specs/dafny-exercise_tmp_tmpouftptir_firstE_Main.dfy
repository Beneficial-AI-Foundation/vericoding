//ATOM
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1

{
  x := 0;
  assume if 'e' in a[..] then 0 <= x < a.Length && a[x] ==> 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x ==> -1;
  return x;
}


// SPEC

method Main() {
	var a: array<char> := new char[]['c','h','e','e','s','e'];
	var res := firstE(a);
	
	a := new char[]['e'];
	res := firstE(a);
	
	a := new char[][];
	res := firstE(a);
}
