// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ATOM 
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype State = State(m:map<int, bool>)
// ATOM 

lemma Test(s:State)
  requires 42 in s.m
  ensures s.(m := s.m[42 := s.m[42]]) == s
{
  var s' := s.(m := s.m[42 := s.m[42]]);
}


// ATOM 

datatype MyDt = MakeA(x: int, bool) | MakeB(s: multiset<int>, t: State)
// ATOM 

lemma AnotherTest(a: MyDt, b: MyDt, c: bool)
  requires a.MakeB? && b.MakeB?
  requires a.s == multiset(a.t.m.Keys) && |b.s| == 0
  requires a.t.m == map[] && |b.t.m| == 0
{
}


// ATOM 

datatype GenDt<X,Y> = Left(X) | Middle(X,int,Y) | Right(y: Y)
// SPEC 

method ChangeGen(g: GenDt)
{
}


// ATOM 

datatype Recursive<X> = Red | Green(next: Recursive, m: set)
// ATOM 

lemma RecLem(r: Recursive) returns (s: Recursive)
  ensures r == s
{
  match r
  case Red =>
    s := Red;
  case Green(next, m) =>
    var n := RecLem(next);
    s := Green(n, m + m);
}




