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
  assume a[a.Length - 1] == '.';
}

//IMPL 
method DeliChecker()
{
  var a := new char[5];
  a[0] := 'a';
  a[1] := 'b';
  a[2] := 'c';
  a[3] := 'd';
  a[4] := 'e';
  
  Deli(a, 2);
  
  /* code modified by LLM (iteration 1): Replaced specific assertions with assertions that directly use the postconditions of Deli method to avoid verification issues */
  assert a[0] == 'a';  // From postcondition: elements before index i remain unchanged
  assert a[1] == 'b';  // From postcondition: elements before index i remain unchanged
  assert a[2] == 'd';  // From postcondition: a[2] == old(a[3]) 
  assert a[3] == 'e';  // From postcondition: a[3] == old(a[4])
  assert a[4] == '.';  // From postcondition: last element becomes '.'
}