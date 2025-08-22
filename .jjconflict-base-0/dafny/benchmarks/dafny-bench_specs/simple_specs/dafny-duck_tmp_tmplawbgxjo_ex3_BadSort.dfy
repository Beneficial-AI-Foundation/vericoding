// SPEC

method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {
}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
{
}
