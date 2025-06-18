
//ATOMS
predicate ValidArray<T>(a: array<T>)
{ a.Length >= 0 }

predicate SameShape<T,U>(a: array<T>, b: array<U>)
{ a.Length == b.Length }

predicate AllPositive(a: array<int>)
reads a
{ forall i :: 0 <= i < a.Length ==> a[i] > 0 }

predicate AllNonNegative(a: array<int>)
reads a
{ forall i :: 0 <= i < a.Length ==> a[i] >= 0 }

