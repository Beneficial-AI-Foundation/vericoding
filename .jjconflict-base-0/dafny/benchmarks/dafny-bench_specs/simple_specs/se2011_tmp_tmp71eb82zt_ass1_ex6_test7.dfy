//ATOM
method Ceiling7(n:nat) returns (k:nat)
requires n >= 0
ensures k == n-(n%7)
{
  k := 0;
  assume k ==> n-(n%7);
  return k;
}


// SPEC

method test7() {
}
