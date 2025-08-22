// ATOM 
predicate derangement(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> s[i] != i
}

// ATOM
predicate permutation(s: seq<nat>) {
    forall x :: x in s ==> 0 <= x < |s|
}

// ATOM
predicate distinct(s: seq<nat>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// ATOM 
function multisetRange(n: nat): multiset<nat> {
    multiset(seq(n, i => i))
}

// IMPL test
method test() {
}