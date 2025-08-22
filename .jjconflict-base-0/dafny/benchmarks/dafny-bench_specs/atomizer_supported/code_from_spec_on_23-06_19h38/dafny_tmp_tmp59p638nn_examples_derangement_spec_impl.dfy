// ATOM 
predicate derangement(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> s[i] != i
}

// ATOM 
predicate permutation(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> i in s
}

// ATOM 
function multisetRange(n: nat): multiset<nat> {
    multiset(seq(n, i => i))
}

// ATOM 
predicate distinct<A(==)>(s: seq<A>) {
    forall x,y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
}

// IMPL test
method test() {
}