// see pdf 'ex6 & 7 documentation' for excercise question


datatype Bases = A | C | G | T

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
  assume{:axiom} false;
}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}

// <vc-helpers>
lemma BelowTransitive(x: Bases, y: Bases, z: Bases)
    requires below(x, y) && below(y, z)
    ensures below(x, z)
{
    // Proof by cases on the values of x, y, z
}

lemma ExchangerPreservesBelow(s: seq<Bases>, x: nat, y: nat, t: seq<Bases>, j: nat, k: nat)
    requires 0 < |s| && x < |s| && y < |s|
    requires |t| == |s|
    requires forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
    requires t[x] == s[y] && t[y] == s[x]
    requires 0 <= j < k < |t|
    requires j != x && j != y && k != x && k != y
    requires below(s[j], s[k])
    ensures below(t[j], t[k])
{
    assert t[j] == s[j] && t[k] == s[k];
}

lemma BelowReflexive(x: Bases)
    ensures below(x, x)
{
}

lemma BelowProperties()
    ensures below(A, A) && below(A, C) && below(A, G) && below(A, T)
    ensures below(C, C) && below(C, G) && below(C, T)
    ensures below(G, G) && below(G, T)
    ensures below(T, T)
    ensures !below(C, A) && !below(G, A) && !below(T, A)
    ensures !below(G, C) && !below(T, C)
    ensures !below(T, G)
{
}

lemma BelowFromValue(x: Bases, y: Bases)
    ensures x == A ==> below(x, y)
    ensures y == T ==> below(x, y)
    ensures x == C && (y == C || y == G || y == T) ==> below(x, y)
    ensures x == G && (y == G || y == T) ==> below(x, y)
    ensures x == y ==> below(x, y)
{
}

lemma ExchangerMaintainsInvariant(sobases: seq<Bases>, a: nat, c: nat, g: nat, i: nat, pos1: nat, pos2: nat, sobases': seq<Bases>)
    requires 0 <= a <= c <= g <= i <= |sobases|
    requires pos1 < |sobases| && pos2 < |sobases|
    requires |sobases'| == |sobases|
    requires forall b:nat :: 0 <= b < |sobases| && b != pos1 && b != pos2 ==> sobases'[b] == sobases[b]
    requires sobases'[pos1] == sobases[pos2] && sobases'[pos2] == sobases[pos1]
    requires forall j :: 0 <= j < a ==> sobases[j] == A
    requires forall j :: a <= j < c ==> sobases[j] == C
    requires forall j :: c <= j < g ==> sobases[j] == G
    requires forall j :: g <= j < i ==> sobases[j] == T
    requires forall j, k :: a <= j < c && c <= k < |sobases| ==> below(sobases[j], sobases[k])
    requires forall j, k :: c <= j < g && g <= k < |sobases| ==> below(sobases[j], sobases[k])
    ensures forall j, k :: a <= j < c && c <= k < |sobases'| ==> below(sobases'[j], sobases'[k])
    ensures forall j, k :: c <= j < g && g <= k < |sobases'| ==> below(sobases'[j], sobases'[k])
{
    forall j, k | a <= j < c && c <= k < |sobases'|
        ensures below(sobases'[j], sobases'[k])
    {
        if j != pos1 && j != pos2 && k != pos1 && k != pos2 {
            assert sobases'[j] == sobases[j];
            assert sobases'[k] == sobases[k];
            assert below(sobases[j], sobases[k]);
        } else {
            assert sobases'[j] == C;
            BelowFromValue(C, sobases'[k]);
        }
    }
    
    forall j, k | c <= j < g && g <= k < |sobases'|
        ensures below(sobases'[j], sobases'[k])
    {
        if j != pos1 && j != pos2 && k != pos1 && k != pos2 {
            assert sobases'[j] == sobases[j];
            assert sobases'[k] == sobases[k];
            assert below(sobases[j], sobases[k]);
        } else {
            assert sobases'[j] == G;
            if g <= k < i {
                assert sobases'[k] == T || k == pos1 || k == pos2;
            }
            BelowFromValue(G, sobases'[k]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
// </vc-spec>
// <vc-code>
{
    sobases := bases;
    var a, c, g, i := 0, 0, 0, 0;
    
    while i < |sobases|
        invariant 0 <= a <= c <= g <= i <= |sobases|
        invariant multiset(bases) == multiset(sobases)
        invariant |sobases| == |bases|
        // Region invariants
        invariant forall j :: 0 <= j < a ==> sobases[j] == A
        invariant forall j :: a <= j < c ==> sobases[j] == C
        invariant forall j :: c <= j < g ==> sobases[j] == G
        invariant forall j :: g <= j < i ==> sobases[j] == T
        // Below invariants for borders between regions
        invariant forall j, k :: 0 <= j < a && a <= k < |sobases| ==> below(sobases[j], sobases[k])
        invariant forall j, k :: a <= j < c && c <= k < |sobases| ==> below(sobases[j], sobases[k])
        invariant forall j, k :: c <= j < g && g <= k < |sobases| ==> below(sobases[j], sobases[k])
    {
        match sobases[i]
        case A =>
            var old_sobases := sobases;
            sobases := Exchanger(sobases, a, i);
            
            // After exchange, position a has A and position i has what was at a
            assert sobases[a] == A;
            
            // Update pointers
            a := a + 1;
            if c < a {
                c := a;
            }
            if g < c {
                g := c;
            }
            i := i + 1;
            
        case C =>
            var old_sobases := sobases;
            sobases := Exchanger(sobases, c, i);
            
            // After exchange, position c has C
            assert sobases[c] == C;
            
            // Update pointers
            c := c + 1;
            if g < c {
                g := c;
            }
            i := i + 1;
            
        case G =>
            var old_sobases := sobases;
            sobases := Exchanger(sobases, g, i);
            
            // After exchange, position g has G
            assert sobases[g] == G;
            
            g := g + 1;
            i := i + 1;
            
        case T =>
            // T is already in the correct position
            i := i + 1;
    }
    
    // Prove bordered from the loop invariants
    assert i == |sobases|;
    assert a <= c <= g <= |sobases|;
    
    forall j, k | 0 <= j < k < |sobases|
        ensures below(sobases[j], sobases[k])
    {
        if j < a {
            assert sobases[j] == A;
            BelowFromValue(A, sobases[k]);
        } else if j < c {
            assert sobases[j] == C;
            if k >= c {
                assert below(sobases[j], sobases[k]);
            } else {
                assert sobases[k] == C;
                BelowFromValue(C, C);
            }
        } else if j < g {
            assert sobases[j] == G;
            if k >= g {
                assert below(sobases[j], sobases[k]);
            } else {
                assert sobases[k] == G;
                BelowFromValue(G, G);
            }
        } else {
            assert sobases[j] == T;
            assert sobases[k] == T;
            BelowFromValue(T, T);
        }
    }
    
    assert bordered(sobases);
}
// </vc-code>

