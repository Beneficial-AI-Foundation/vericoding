// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

 f(x:int):int { x }

// ATOM 

lemma L()
    ensures forall x:int :: f(x) == x
{
    forall x:int
        ensures f(x) == x
    {
        reveal f();
    }
}






