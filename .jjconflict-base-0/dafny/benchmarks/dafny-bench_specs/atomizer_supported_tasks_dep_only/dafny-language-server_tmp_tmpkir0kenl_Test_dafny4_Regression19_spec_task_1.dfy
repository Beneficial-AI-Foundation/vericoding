// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM_PLACEHOLDER_ContainsNothingBut5

//ATOM_PLACEHOLDER_YeahContains5

//ATOM_PLACEHOLDER_ViaSetComprehension

//ATOM_PLACEHOLDER_LambdaTest

//ATOM_PLACEHOLDER_ViaMapComprehension

//ATOM_PLACEHOLDER_Contains5

//ATOM_PLACEHOLDER_R//ATOM_PLACEHOLDER_RIs5

//ATOM_PLACEHOLDER_NonemptySet
//ATOM_PLACEHOLDER_NonemptyMap

// SPEC 

method M(s: set<int>, r: R, q: int)
  requires s == {
}
{
}
 && r == MakeR(5)
{

  NonemptySet(5, set q | q in s && q == 5);

  NonemptyMap(5, map q | q in s && q == 5 :: true);


}

 && r == MakeR(5)
{

  NonemptySet(5, set q | q in s && q == 5);

  NonemptyMap(5, map q | q in s && q == 5 :: true);


}

