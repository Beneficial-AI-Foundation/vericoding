//ATOM
predicate sortedbad(s: string)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

//IMPL 
method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
{
    // Since the precondition requires all characters to be in an empty set,
    // the only valid input is an empty string
    b := a;
}