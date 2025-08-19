//ATOM

predicate derangement(s: seq<nat>) {
  forall i :: 0 <= i < |s| ==> s[i] != i
}


//ATOM

function multisetRange(n: nat): multiset<nat> {
  multiset(seq(n, i => i))
}


// SPEC

method test() {
}
