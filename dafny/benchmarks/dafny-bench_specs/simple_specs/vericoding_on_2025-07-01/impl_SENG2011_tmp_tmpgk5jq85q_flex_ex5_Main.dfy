//ATOM
method firste(a: array<char>) returns (c:int)
ensures -1 <= c < a.Length
ensures 0 <= c < a.Length ==> a[c] == 'e' && forall x :: 0 <= x < c ==> a[x] != 'e'
ensures c == -1 ==> forall x :: 0 <= x < a.Length ==> a[x] != 'e'
{
  c := 0;
  assume -1 <= c < a.Length;
  assume 0 <= c < a.Length ==> a[c] == 'e' && forall x :: 0 <= x < c ==> a[x] != 'e';
  assume c == -1 ==> forall x :: 0 <= x < a.Length ==> a[x] != 'e';
  return c;
}

//IMPL
method Main(){
  var a := new char[6]['c','h','e','e','s','e'];
  var p := firste(a);
  print p;
}