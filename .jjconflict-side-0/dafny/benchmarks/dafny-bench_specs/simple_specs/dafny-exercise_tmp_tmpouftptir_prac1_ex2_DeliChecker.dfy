//ATOM
method Deli(a: array<char>, i: nat)
modifies a
requires a.Length > 0
requires 0 <= i < a.Length
ensures forall j :: 0 <= j < i ==> a[j] == old(a[j])
ensures forall j :: i <= j < a.Length - 1 ==> a[j] == old(a[j + 1])
ensures a[a.Length - 1] == '.'
{
  assume forall j :: 0 <= j < i ==> a[j] == old(a[j]);
  assume forall j :: i <= j < a.Length - 1 ==> a[j] == old(a[j + 1]);
  assume a[a.Length - 1] ==> '.';
}


// SPEC

method DeliChecker()
{
}
