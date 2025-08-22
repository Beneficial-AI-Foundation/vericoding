// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ATOM 
// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate ContainsNothingBut5(s: set<int>)
{
  forall q :: q in s ==> q == 5
}


// ATOM 

predicate YeahContains5(s: set<int>)
{
  exists q :: q in s && q == 5
}


// ATOM 

predicate ViaSetComprehension(s: set<int>) {
  |set q | q in s && q == 5| != 0
}


// ATOM 

predicate LambdaTest(s: set<int>) {
  (q => q in s)(5)
}


// ATOM 

predicate ViaMapComprehension(s: set<int>) {
  |(map q | q in s && q == 5 :: true).Keys| != 0
}


// ATOM 

predicate Contains5(s: set<int>)
{
  var q := 5; q in s
}


// ATOM 

datatype R = MakeR(int) | Other
// ATOM 

predicate RIs5(r: R) {
  match r case MakeR(q) => q == 5 case Other => false
}


// ATOM 

lemma NonemptySet(x: int, s: set<int>)
  requires x in s
  ensures |s| != 0
{
}

// ATOM 
lemma NonemptyMap(x: int, s: map<int,bool>)
  requires x in s.Keys
  ensures |s| != 0
{
}


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

