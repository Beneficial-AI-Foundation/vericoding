// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM ContainsNothingBut5
predicate ContainsNothingBut5(s: set<int>)
{
  forall x :: x in s ==> x == 5
}

//ATOM YeahContains5
predicate YeahContains5(s: set<int>)
{
  5 in s
}

//ATOM ViaSetComprehension
function ViaSetComprehension(s: set<int>): set<int>
{
  set q | q in s && q == 5
}

//ATOM LambdaTest
function LambdaTest(s: set<int>): map<int, bool>
{
  map q | q in s && q == 5 :: true
}

//ATOM ViaMapComprehension
function ViaMapComprehension(s: set<int>): map<int, bool>
{
  map q | q in s && q == 5 :: true
}

//ATOM Contains5
predicate Contains5(s: set<int>)
{
  5 in s
}

//ATOM R
datatype R = MakeR(value: int)

//ATOM RIs5
predicate RIs5(r: R)
{
  r.value == 5
}

//ATOM NonemptySet
lemma NonemptySet(x: int, s: set<int>)
  requires x in s
  ensures s != {}
{
}

//ATOM NonemptyMap
lemma NonemptyMap(x: int, m: map<int, bool>)
  requires x in m
  ensures m != map[]
{
}

//IMPL SPEC
method M(s: set<int>, r: R, q: int)
  requires s == {5} && r == MakeR(5)
{
  NonemptySet(5, set q | q in s && q == 5);
  NonemptyMap(5, map q | q in s && q == 5 :: true);
}