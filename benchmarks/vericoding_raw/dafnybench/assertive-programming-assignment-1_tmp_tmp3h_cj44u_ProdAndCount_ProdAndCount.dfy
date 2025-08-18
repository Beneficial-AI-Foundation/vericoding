lemma AppendOne<T>(q: seq<T>, n: nat)
    requires n < |q|
    ensures q[..n]+[q[n]] == q[..n+1]
{}

function RecursivePositiveProduct(q: seq<int>): int
    decreases |q|
{
    if q == [] then 1
    else if q[0] <= 0 then RecursivePositiveProduct(q[1..])
    else q[0] * RecursivePositiveProduct(q[1..])
}

function RecursiveCount(key: int, q: seq<int>): int
    decreases |q|
{
    if q == [] then 0
    else if q[|q|-1] == key then 1+RecursiveCount(key, q[..|q|-1])
    else RecursiveCount(key, q[..|q|-1])
}

// <vc-helpers>
// </vc-helpers>

method ProdAndCount(q: seq<int>, key: int) returns (prod: int, count: nat)
    ensures prod == RecursivePositiveProduct(q)
    ensures count == RecursiveCount(key, q)
// <vc-code>
{
  assume false;
}
// </vc-code>

function county(elem: int, key: int): int{
    if elem==key then 1 else 0
}

function prody(elem: int): int{
    if elem <= 0 then 1 else elem
}

lemma Lemma_Count_Inv(q: seq<int>, i: nat, count: int, key: int)
    requires 0 <= i < |q| && count == RecursiveCount(key, q[..i])
    ensures 0 <= i+1 <= |q| && county(q[i],key)+count == RecursiveCount(key, q[..i+1])
{
    assert q[..i+1] == q[..i] + [q[i]];
    var q1 := q[..i+1];
    calc {
            RecursiveCount(key, q[..i+1]);
            == // def.
                if q1 == [] then 0
                else if q1[i] == key then 1+RecursiveCount(key,q1[..i])
                else RecursiveCount(key, q1[..i]);
            == { assert q1 != []; } // simplification for a non-empty sequence
                if q1[i] == key then 1+RecursiveCount(key, q1[..i])
                else RecursiveCount(key,q1[..i]);
            == {KibutzLaw1(q1,key,i);} // the kibutz law 
                (if q1[i] == key then 1 else 0) + RecursiveCount(key, q1[..i]);
            == 
                county(q1[i],key) + RecursiveCount(key, q1[..i]);
            ==
                county(q[i],key) + RecursiveCount(key, q[..i]);
    }

}


lemma Lemma_Prod_Inv(q: seq<int>, i: nat, prod: int)
    requires 0 <= i < |q| && prod == RecursivePositiveProduct(q[..i])
    ensures 0 <= i+1 <= |q| && prody(q[i])*prod == RecursivePositiveProduct(q[..i+1])
{
    assert q[..i+1] == q[..i] + [q[i]];
    var q1 := q[..i+1];
    calc {
        RecursivePositiveProduct(q[..i+1]);
    == // def.
        if q1 == [] then 1
        else if q1[0] <= 0 then RecursivePositiveProduct(q1[1..])
        else q1[0] * RecursivePositiveProduct(q1[1..]);
    == { assert q1 != []; } // simplification for a non-empty sequence
        if q1[0] <= 0 then RecursivePositiveProduct(q1[1..])
        else q1[0] * RecursivePositiveProduct(q1[1..]);
    == // def. of q1
        if q[0] <= 0 then RecursivePositiveProduct(q[1..i+1])
        else q[0] * RecursivePositiveProduct(q[1..i+1]);
    == { KibutzLaw2(q);}
        (if q[0] <= 0 then 1 else q[0])*RecursivePositiveProduct(q[1..i+1]);
    ==
        prody(q[0])*RecursivePositiveProduct(q[1..i+1]);
    == {PrependProd(q);}
        RecursivePositiveProduct(q[..i+1]);
    == {AppendProd(q[..i+1]);}
        prody(q[i])*RecursivePositiveProduct(q[..i]);
    ==
        prody(q[i])*prod;
    }
}

lemma Lemma_Count_Finish(q: seq<int>, i: nat, count: int, key: int)
    requires inv: 0 <= i <= |q| && count == RecursiveCount(key, q[..i])
    requires neg_of_guard: i >= |q|
    ensures count == RecursiveCount(key, q)
{
    assert i <= |q| && count == RecursiveCount(key, q[..i]) by { reveal inv; }
    assert i == |q| by { reveal inv,neg_of_guard; }
    assert q[..i] == q[..|q|] == q;
}

lemma Lemma_Prod_Finish(q: seq<int>, i: nat, prod: int)
    requires inv: 0 <= i <= |q| && prod == RecursivePositiveProduct(q[..i])
    requires neg_of_guard: i >= |q|
    ensures prod == RecursivePositiveProduct(q)
{
    assert i <= |q| && prod == RecursivePositiveProduct(q[..i]) by { reveal inv; }
    assert i == |q| by { reveal inv,neg_of_guard; }
    assert q[..i] == q[..|q|] == q;
}

lemma KibutzLaw1(q: seq<int>,key: int,i: nat)
requires q != [] && i < |q|
ensures         
    (if q[|q|-1] == key then 1 + RecursiveCount(key, q[1..i+1])
    else 0 + RecursiveCount(key, q[1..i+1]))
    == 
    (if q[|q|-1] == key then 1 else 0) + RecursiveCount(key, q[1..i+1])
{
    if q[|q|-1] == key {
        calc {
            (if q[|q|-1] == key then 1 + RecursiveCount(key, q[1..i+1])
            else 0 + RecursiveCount(key, q[1..i+1]));
            ==
            1 + RecursiveCount(key, q[1..i+1]);
            ==
            (if q[|q|-1] == key then 1 else 0) + RecursiveCount(key, q[1..i+1]);
        }
    } else {
        calc {
            (if q[|q|-1] == key then 1 + RecursiveCount(key, q[1..i+1])
            else 0 + RecursiveCount(key, q[1..i+1]));
            ==
            0 + RecursiveCount(key, q[1..i+1]);
            ==
            (if q[|q|-1] == key then 1 else 0) + RecursiveCount(key, q[1..i+1]);
        }
    }

}

lemma KibutzLaw2(q: seq<int>)
requires q != [] 
ensures         
    (if q[0] <= 0 then RecursivePositiveProduct(q[1..])
        else q[0] * RecursivePositiveProduct(q[1..]))
    == 
    (if q[0] <= 0 then 1 else q[0])*RecursivePositiveProduct(q[1..])
{
    if q[0] <= 0 {
        calc {
        (if q[0] <= 0 then RecursivePositiveProduct(q[1..])
            else q[0] * RecursivePositiveProduct(q[1..]));
            ==
            RecursivePositiveProduct(q[1..]);
            ==
            (if q[0] <= 0 then 1 else q[0])*RecursivePositiveProduct(q[1..]);
        }
    } else {
        calc {
        (if q[0] <= 0 then RecursivePositiveProduct(q[1..])
            else q[0] * RecursivePositiveProduct(q[1..]));
            ==
            q[0] * RecursivePositiveProduct(q[1..]);
            ==
            (if q[0] <= 0 then 1 else q[0])*RecursivePositiveProduct(q[1..]);
        }
    }
}

lemma AppendCount(key: int, q: seq<int>)
    requires q != [] 
    ensures RecursiveCount(key, q) == RecursiveCount(key,q[..|q|-1])+county(q[|q|-1], key)  
{
    if |q| == 1
    {
        assert
        RecursiveCount(key,q[..|q|-1])+county(q[|q|-1], key) == 
        RecursiveCount(key,q[..0])+county(q[0], key) == 
        RecursiveCount(key, [])+county(q[0], key) ==
        0+county(q[0], key) == 
        county(q[0], key);
        assert RecursiveCount(key, q) == county(q[0], key);
    }
    else
    {       // inductive step
        var q1 := q[1..];
        calc {
            RecursiveCount(key, q);
        == // def. for a non-empty sequence
            if q == [] then 0
            else if q[|q|-1] == key then 1+RecursiveCount(key, q[..|q|-1])
            else RecursiveCount(key, q[..|q|-1]);
        ==  
            RecursiveCount(key, q[..|q|-1]) + county(q[|q|-1], key);
        }
    }
}

lemma PrependProd(q: seq<int>)
    requires q != []
    ensures RecursivePositiveProduct(q) == prody(q[0])*RecursivePositiveProduct(q[1..])
{
    calc {
            RecursivePositiveProduct(q);
        == 
            if q == [] then 1
            else if q[0] <= 0 then RecursivePositiveProduct(q[1..])
            else q[0] * RecursivePositiveProduct(q[1..]);
        == { assert q != []; } // simplification for a non-empty sequence
            if q[0] <= 0 then RecursivePositiveProduct(q[1..])
            else q[0] * RecursivePositiveProduct(q[1..]);
        == { KibutzLaw2(q);}
            (if q[0] <= 0 then 1 else q[0])*RecursivePositiveProduct(q[1..]);
        ==
            prody(q[0])*RecursivePositiveProduct(q[1..]);
        }
}

lemma AppendProd(q: seq<int>)
    requires q != [] 
    ensures RecursivePositiveProduct(q) == RecursivePositiveProduct(q[..|q|-1])*prody(q[|q|-1]) 
{
    if |q| == 1
    {
        assert
        RecursivePositiveProduct(q[..|q|-1])*prody(q[|q|-1]) == 
        RecursivePositiveProduct(q[..0])*prody(q[0]) == 
        RecursivePositiveProduct([])*prody(q[0]) ==
        1*prody(q[0]) == 
        prody(q[0]);
        assert RecursivePositiveProduct(q) == prody(q[0]);
    }
    else
    {       // inductive step
        var q1 := q[1..];
        calc {
            RecursivePositiveProduct(q);
        == // def. for a non-empty sequence
            prody(q[0]) * RecursivePositiveProduct(q[1..]);
        == { assert q1 != []; assert |q1| < |q|; AppendProd(q1); } // induction hypothesis (one assertion for the precondition, another for termination)
            prody(q[0]) * RecursivePositiveProduct(q1[..|q1|-1]) * prody(q1[|q1|-1]);
        == { assert q1[..|q1|-1] == q[1..|q|-1]; assert q1[|q1|-1] == q[|q|-1]; }
            prody(q[0]) * RecursivePositiveProduct(q[1..|q|-1])  * prody(q[|q|-1]);
        == {PrependProd(q[..|q|-1]);}
            RecursivePositiveProduct(q[..|q|-1])  * prody(q[|q|-1]);
        }
    }
}