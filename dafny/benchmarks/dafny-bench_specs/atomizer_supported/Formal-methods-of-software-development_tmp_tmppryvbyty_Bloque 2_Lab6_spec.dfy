/*predicate palindrome<T(==)> (s:seq<T>)
{
    forall i:: 0<=i<|s| ==> s[i] == s[|s|-i-1]
}
*/
// SUM OF A SEQUENCE OF INTEGERS
// ATOM 
// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
{
    if v==[] then 0
    else if |v|==1 then v[0]
    else v[0]+sum(v[1..])
}

/*


/*
// SPEC 
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v) 
{
}


// Structural Induction on Sequences
// ATOM 

// Structural Induction on Sequences
lemma left_sum_Lemma(r:seq<int>, k:int)
requires 0 <= k < |r|
ensures sum(r[..k]) + r[k] == sum(r[..k+1]);
{
    if |r|==1 || k==0{
    }
    else {
        left_sum_Lemma(r[1..], k);

        calc {
            sum(r[..k+1]);
            sum(r[..k]) + [r[k]];
        }
    }
}


// MAXIMUM OF A SEQUENCE
// SPEC 

// MAXIMUM OF A SEQUENCE
method maxSeq(v: seq<int>) returns (max:int)
requires |v| >= 1
ensures forall i :: 0 <= i < |v| ==> max >= v[i]
ensures max in v
{
}


// TODO: Hacer
// Derivar formalmente un calculo incremental de j*j*j
// SPEC 

// TODO: Hacer
// Derivar formalmente un calculo incremental de j*j*j
method Cubes (n:int) returns (s:seq<int>)
requires n >= 0
ensures |s| == n
ensures forall i:int :: 0 <= i < n ==> s[i] == i*i*i
{
}



// REVERSE OF A SEQUENCE
// ATOM 


// REVERSE OF A SEQUENCE
function reverse<T> (s:seq<T>):seq<T> 
{
    if s==[] then []
    else reverse(s[1..])+[s[0]]
}


// ATOM 

function seq2set<T> (s:seq<T>): set<T>
{
    if s==[] then {}
    else {s[0]}+seq2set(s[1..])
}



// ATOM 


lemma seq2setRev_Lemma<T> (s:seq<T>)
ensures seq2set(reverse(s)) == seq2set(s)
{
    if s==[]{}
    else {
        seq2setRev_Lemma(s[1..]);

        calc {
            seq2set(s);
            seq2set([s[0]]+s[1..]);
            {
                concat_seq2set_Lemma([s[0]], s[1..]);
            }
            seq2set([s[0]]) + seq2set(s[1..]);
            {
                seq2setRev_Lemma(s[1..]);
            }
            seq2set([s[0]]) + seq2set(reverse(s[1..]));
            seq2set(reverse(s[1..])) + seq2set([s[0]]); 
            {
                concat_seq2set_Lemma(reverse(s[1..]), [s[0]]);
            }
            seq2set(reverse(s[1..]) + [s[0]]);
            {
            }
            seq2set(reverse(s));
        }
    }
}



// ATOM 


lemma concat_seq2set_Lemma<T>(s1:seq<T>,s2:seq<T>)
ensures seq2set(s1+s2) == seq2set(s1) + seq2set(s2)
{
    if s1==[]{
    }
    else {
        concat_seq2set_Lemma(s1[1..], s2);

        calc{
            seq2set(s1) + seq2set(s2);
            seq2set([s1[0]]+s1[1..]) + seq2set(s2);
            seq2set([s1[0]]) + seq2set(s1[1..]) + seq2set(s2);
            {
                concat_seq2set_Lemma(s1[1..], s2);
            }
            seq2set([s1[0]]) + seq2set(s1[1..]+s2);
            {
            }
            seq2set([s1[0]]) + seq2set((s1+s2)[1..]);
            {
                // assert seq2set([s1[0]]) + seq2set((s1+s2)[1..]) == seq2set(s1+s2);
                var ls:= s1+s2;
                calc {
                    seq2set([s1[0]]) + seq2set((s1+s2)[1..]);
                    seq2set([ls[0]])+ seq2set(ls[1..]);
                    seq2set([ls[0]]+ ls[1..]);
                    seq2set(ls);
                    seq2set(s1+s2);
                }
            }
            seq2set(s1+s2);
        }
    }
}



// REVERSE IS ITS OWN INVERSE

// ATOM 


// REVERSE IS ITS OWN INVERSE

lemma Rev_Lemma<T(==)>(s:seq<T>)
// ATOM 
//ensures forall i :: 0 <= i < |s| ==> s[i] == reverse(s)[|s|-1-i]

lemma ItsOwnInverse_Lemma<T> (s:seq<T>)
ensures s == reverse(reverse(s))
{
    if s==[]{}
    else{
        ItsOwnInverse_Lemma(s[1..]);

        calc {
            reverse(reverse(s));
            reverse(reverse(s[1..])+[s[0]]);
            reverse(reverse([s[0]]+s[1..]));
            {
            }
            reverse(reverse(s[1..]) + [s[0]]);
            {
                // TODO: Demostrar este assume
                assume reverse(reverse(s[1..]) + [s[0]]) == [s[0]] + reverse(reverse(s[1..]));
            }
            [s[0]] + reverse(reverse(s[1..]));
            {
                ItsOwnInverse_Lemma(s[1..]);
            }
            [s[0]]+s[1..];
            s;
        }
    }
}


// SCALAR PRODUCT OF TWO VECTORS OF INTEGER
// ATOM 

// SCALAR PRODUCT OF TWO VECTORS OF INTEGER
function scalar_product (v1:seq<int>, v2:seq<int>):int
requires |v1| == |v2|
{
    if v1 == [] then 0 else v1[0]*v2[0] + scalar_product(v1[1..],v2[1..])
}



// ATOM 


lemma scalar_product_Lemma (v1:seq<int>, v2:seq<int>)
requires |v1| == |v2| > 0
ensures scalar_product(v1,v2) == scalar_product(v1[..|v1|-1],v2[..|v2|-1]) + v1[|v1|-1] * v2[|v2|-1]
{
    // INDUCCION EN LA LONGITUD DE V1
    if |v1| == 0 && |v2| == 0 {}
    else if |v1| == 1 {}
    else {
        // Se crean estas variables para simplificar las operaciones
        var v1r:= v1[1..];
        var v2r:= v2[1..];
        var t1:= |v1[1..]|-1;
        var t2:= |v2[1..]|-1;

        // Se realiza la induccion utilizando las variables
        scalar_product_Lemma(v1r, v2r);
                scalar_product(v1r[..t1],v2r[..t2]) + v1r[t1] * v2r[t2]; //HI
        
        // Se demuestra que la propiedad se mantiene
        calc{
            scalar_product(v1,v2);
            v1[0]*v2[0] + scalar_product(v1r, v2r);
            v1[0]*v2[0] + scalar_product(v1r[..t1],v2r[..t2]) + v1r[t1] * v2r[t2];
            {
                scalar_product_Lemma(v1r, v2r);
                        scalar_product(v1r[..t1],v2r[..t2]) + v1r[t1] * v2r[t2]; //HI
            }
            v1[0]*v2[0] + scalar_product(v1r,v2r);
            v1[0]*v2[0] + scalar_product(v1[1..],v2[1..]);
            scalar_product(v1,v2);
        }
    }
}


// MULTISETS

// SPEC 

// MULTISETS

method multiplicity_examples<T> ()
{
}


// REVERSE HAS THE SAME MULTISET 

// ATOM 

// REVERSE HAS THE SAME MULTISET 

lemma seqMultiset_Lemma<T> (s:seq<T>)
ensures multiset(reverse(s)) == multiset(s)
{
    if s==[]{}
    else {
        seqMultiset_Lemma(s[1..]);

        calc {
            multiset(reverse(s));
            multiset(reverse(s[1..]) + [s[0]]);
            multiset(reverse(s[1..])) + multiset{[s[0]]};
            multiset(s[1..]) + multiset{[s[0]]};
            multiset(s);
        }
    }
}
*/

*/
// ATOM 
lemma empty_Lemma<T> (r:seq<T>)
requires  multiset(r) == multiset{} 
ensures r == []
{
	if r != []	{
	}
}
 
ensures r == []
{
	if r != []	{
	}
}

// ATOM 

lemma elem_Lemma<T> (s:seq<T>,r:seq<T>)
requires s != [] && multiset(s) == multiset(r)
ensures exists i :: 0 <= i < |r| && r[i] == s[0] && multiset(s[1..]) == multiset(r[..i]+r[i+1..]);
// ATOM 

// SEQUENCES WITH EQUAL MULTISETS HAVE EQUAL SUMS

lemma sumElems_Lemma(s:seq<int>, r:seq<int>)   
requires multiset(s) == multiset(r)
ensures sum(s) == sum(r)
{
    if s==[]{
        empty_Lemma(r);
    }
    else {
        // Con este lema demuestro que el elemento que le quito a s tambien se lo quito a r y de esta manera
        // poder hacer la induccion
        elem_Lemma(s,r);
		var i :| 0 <= i < |r| && r[i] == s[0] && multiset(s[1..]) == multiset(r[..i]+r[i+1..]);
		sumElems_Lemma(s[1..], r[..i]+r[i+1..]);
        
        // Hago la llamada recursiva
        sumElems_Lemma(s[1..], r[..i]+r[i+1..]);

        calc {
            sum(s);
            s[0]+sum(s[1..]);
            {
                sumElems_Lemma(s[1..], r[..i]+r[i+1..]);
            }
            s[0]+sum(r[..i]+r[i+1..]);
            {
            }
            r[i]+sum(r[..i]+r[i+1..]);
            {
                // TODO: No consigo acertarlo
                assume r[i]+sum(r[..i]+r[i+1..]) == sum([r[i]]+r[..i] + r[i+1..]) == sum(r);
            }
            sum(r);
        }
    }
}


