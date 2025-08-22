// see pdf 'ex6 & 7 documentation' for excercise question

//ATOM Bases
datatype Bases = A | T | G | C

//IMPL 
//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
    /* code modified by LLM (iteration 3): store original values before swapping to ensure correct swap */
    var temp_x := s[x];
    var temp_y := s[y];
    t := s[x := temp_y][y := temp_x];
}

/* code modified by LLM (iteration 1): added comparison function for Bases datatype */
function BaseValue(b: Bases): int
{
    match b
        case A => 0
        case T => 1
        case G => 2
        case C => 3
}

/* code modified by LLM (iteration 1): added comparison predicate for Bases */
predicate BaseLessEq(b1: Bases, b2: Bases)
{
    BaseValue(b1) <= BaseValue(b2)
}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
//ATOM below
predicate below(s: seq<Bases>, i: nat, b: Bases)
{
    forall k :: 0 <= k < i && k < |s| ==> BaseLessEq(s[k], b)
}

//checks if a sequence is in base order
//ATOM bordered  
predicate bordered(s: seq<Bases>, i: nat, j: nat, b1: Bases, b2: Bases)
{
    forall k :: i <= k < j && k < |s| ==> BaseLessEq(b1, s[k]) && BaseLessEq(s[k], b2)
}

//ATOM Sorter
method Sorter(s: seq<Bases>) returns (t: seq<Bases>)
requires true
ensures |t| == |s|
ensures multiset(s) == multiset(t)
ensures forall i, j :: 0 <= i < j < |t| ==> BaseLessEq(t[i], t[j])
{
}

//IMPL 
method Testerexchange() {
    /* code modified by LLM (iteration 2): added proper test implementation with correct assertions */
    var s := [A, T, G, C];
    var result := Exchanger(s, 0, 2);
    // The result should swap positions 0 and 2: [A,T,G,C] -> [G,T,A,C]
    assert result[0] == G && result[2] == A;
    assert result[1] == T && result[3] == C;
    assert multiset(s) == multiset(result);
}

//ATOM Testsort
method Testsort() {
    var s := [G, A, T, C, A];
    var sorted := Sorter(s);
    assert multiset(s) == multiset(sorted);
    assert forall i, j :: 0 <= i < j < |sorted| ==> BaseLessEq(sorted[i], sorted[j]);
}