//ATOM
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype State = State(m:map<int, bool>)


//ATOM

datatype MyDt = MakeA(x: int, bool) | MakeB(s: multiset<int>, t: State)


//ATOM

datatype GenDt<X,Y> = Left(X) | Middle(X,int,Y) | Right(y: Y)


//ATOM

datatype Recursive<X> = Red | Green(next: Recursive, m: set)


//IMPL ChangeGen

method ChangeGen(g: GenDt)
{
}