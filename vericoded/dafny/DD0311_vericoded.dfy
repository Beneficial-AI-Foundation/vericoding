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
lemma sum_prop(v: seq<int>, i: int)
    requires 0 <= i <= |v|
    ensures sum(v[..i]) + sum(v[i..]) == sum(v)
{
    if i == 0 {
        assert v[..0] == [];
        assert v[0..] == v;
    } else if i == |v| {
        assert v[..|v|] == v;
        assert v[|v|..] == [];
    } else if |v| == 1 {
        assert i == 0 || i == 1;
        if i == 1 {
            assert v[..1] == [v[0]];
            assert v[1..] == [];
        }
    } else {
        if i == 1 {
            assert v[..1] == [v[0]];
            calc {
                sum(v[..1]) + sum(v[1..]);
                == sum([v[0]]) + sum(v[1..]);
                == { assert |[v[0]]| == 1; }
                   v[0] + sum(v[1..]);
                == sum(v);
            }
        } else {
            calc {
                sum(v[..i]);
                == { assert v[..i] == [v[0]] + v[1..i]; }
                   sum([v[0]] + v[1..i]);
                == { sum_concat_lemma([v[0]], v[1..i]); }
                   sum([v[0]]) + sum(v[1..i]);
                == v[0] + sum(v[1..i]);
            }
            sum_prop(v[1..], i-1);
            calc {
                sum(v[..i]) + sum(v[i..]);
                == v[0] + sum(v[1..i]) + sum(v[i..]);
                == { assert (v[1..])[i-1..] == v[i..]; }
                   v[0] + sum(v[1..i]) + sum((v[1..])[i-1..]);
                == { assert v[1..i] == (v[1..])[..i-1]; }
                   v[0] + sum((v[1..])[..i-1]) + sum((v[1..])[i-1..]);
                == v[0] + sum(v[1..]);
                == sum(v);
            }
        }
    }
}

lemma sum_concat_lemma(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if s1 == [] {
        assert s1 + s2 == s2;
    } else if |s1| == 1 {
        calc {
            sum(s1 + s2);
            == sum([s1[0]] + s2);
            == s1[0] + sum(s2);
            == sum(s1) + sum(s2);
        }
    } else {
        calc {
            sum(s1 + s2);
            == { assert s1 + s2 == [s1[0]] + (s1[1..] + s2); }
               sum([s1[0]] + (s1[1..] + s2));
            == s1[0] + sum(s1[1..] + s2);
            == { sum_concat_lemma(s1[1..], s2); }
               s1[0] + sum(s1[1..]) + sum(s2);
            == sum(s1) + sum(s2);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v)
// </vc-spec>
// <vc-code>
{
    x := 0;
    var i := 0;
    while i < |v|
        invariant 0 <= i <= |v|
        invariant x == sum(v[..i])
    {
        assert v[..i+1] == v[..i] + [v[i]];
        sum_concat_lemma(v[..i], [v[i]]);
        x := x + v[i];
        i := i + 1;
    }
    assert v[..|v|] == v;
}
// </vc-code>

