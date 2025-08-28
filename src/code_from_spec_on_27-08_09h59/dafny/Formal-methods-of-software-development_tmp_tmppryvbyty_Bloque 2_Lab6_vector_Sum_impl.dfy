/*predicate palindrome<T(==)> (s:seq<T>)
{
    forall i:: 0<=i<|s| ==> s[i] == s[|s|-i-1]
}
*/
// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
decreases v
{
    if v==[] then 0
    else if |v|==1 then v[0]
    else v[0]+sum(v[1..])
}

// Structural Induction on Sequences

// MAXIMUM OF A SEQUENCE

// TODO: Hacer
// Derivar formalmente un calculo incremental de j*j*j


// REVERSE OF A SEQUENCE
function reverse<T> (s:seq<T>):seq<T> 
{
    if s==[] then []
    else reverse(s[1..])+[s[0]]
}

function seq2set<T> (s:seq<T>): set<T>
{
    if s==[] then {}
    else {s[0]}+seq2set(s[1..])
}


// REVERSE IS ITS OWN INVERSE

// SCALAR PRODUCT OF TWO VECTORS OF INTEGER
function scalar_product (v1:seq<int>, v2:seq<int>):int
requires |v1| == |v2|
{
    if v1 == [] then 0 else v1[0]*v2[0] + scalar_product(v1[1..],v2[1..])
}

// MULTISETS

method multiplicity_examples<T> ()
{
  assume{:axiom} false;
}

// REVERSE HAS THE SAME MULTISET

// <vc-helpers>
lemma sum_append(v1: seq<int>, v2: seq<int>)
    ensures sum(v1 + v2) == sum(v1) + sum(v2)
{
    if v1 == [] {
        assert v1 + v2 == v2;
    } else if |v1| == 1 {
        assert v1 + v2 == [v1[0]] + v2;
        assert sum(v1 + v2) == v1[0] + sum(v2);
        assert sum(v1) == v1[0];
    } else {
        assert v1 + v2 == [v1[0]] + (v1[1..] + v2);
        sum_append(v1[1..], v2);
    }
}

lemma sum_single(x: int)
    ensures sum([x]) == x
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if |v| == 0 {
        x := 0;
    } else {
        x := 0;
        var i := 0;
        while i < |v|
            invariant 0 <= i <= |v|
            invariant x == sum(v[..i])
        {
            x := x + v[i];
            i := i + 1;
            
            assert v[..i] == v[..i-1] + [v[i-1]];
            sum_append(v[..i-1], [v[i-1]]);
        }
        assert v[..|v|] == v;
    }
}
// </vc-code>
