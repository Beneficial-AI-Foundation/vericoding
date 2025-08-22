// see pdf 'ex6 & 7 documentation' for excercise question

//ATOM_PLACEHOLDER_Bases// SPEC 

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
}


//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
//ATOM_PLACEHOLDER_below

//checks if a sequence is in base order
//ATOM_PLACEHOLDER_bordered

//ATOM_PLACEHOLDER_Sorter

// SPEC 

method Testerexchange() {
}


//ATOM_PLACEHOLDER_Testsort



