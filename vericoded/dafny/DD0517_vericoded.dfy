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

function county(elem: int, key: int): int{
    if elem==key then 1 else 0
}

function prody(elem: int): int{
    if elem <= 0 then 1 else elem
}

// <vc-helpers>
lemma RecursivePositiveProductAppend(q: seq<int>, elem: int)
    ensures RecursivePositiveProduct(q + [elem]) == RecursivePositiveProduct(q) * prody(elem)
{
    if q == [] {
        assert q + [elem] == [elem];
        calc {
            RecursivePositiveProduct([elem]);
            == { if elem <= 0 {
                    assert RecursivePositiveProduct([elem]) == RecursivePositiveProduct([elem][1..]) == RecursivePositiveProduct([]) == 1;
                 } else {
                    assert RecursivePositiveProduct([elem]) == elem * RecursivePositiveProduct([elem][1..]) == elem * RecursivePositiveProduct([]) == elem * 1 == elem;
                 }
               }
               prody(elem);
            == 1 * prody(elem);
            == RecursivePositiveProduct([]) * prody(elem);
        }
    } else {
        var first := q[0];
        var rest := q[1..];
        assert q == [first] + rest;
        assert q + [elem] == [first] + (rest + [elem]);
        
        if first <= 0 {
            calc {
                RecursivePositiveProduct(q + [elem]);
                == RecursivePositiveProduct([first] + (rest + [elem]));
                == { assert [first] + (rest + [elem]) == [first] + rest + [elem]; }
                   RecursivePositiveProduct([first] + rest + [elem]);
                == RecursivePositiveProduct((rest + [elem])[0..]);
                == RecursivePositiveProduct(rest + [elem]);
                == { RecursivePositiveProductAppend(rest, elem); }
                   RecursivePositiveProduct(rest) * prody(elem);
                == RecursivePositiveProduct(q) * prody(elem);
            }
        } else {
            calc {
                RecursivePositiveProduct(q + [elem]);
                == RecursivePositiveProduct([first] + (rest + [elem]));
                == first * RecursivePositiveProduct(rest + [elem]);
                == { RecursivePositiveProductAppend(rest, elem); }
                   first * RecursivePositiveProduct(rest) * prody(elem);
                == RecursivePositiveProduct(q) * prody(elem);
            }
        }
    }
}

lemma RecursiveCountAppend(key: int, q: seq<int>, elem: int)
    ensures RecursiveCount(key, q + [elem]) == RecursiveCount(key, q) + county(elem, key)
{
    if q == [] {
        assert q + [elem] == [elem];
        if elem == key {
            calc {
                RecursiveCount(key, [elem]);
                == 1 + RecursiveCount(key, [elem][..|[elem]|-1]);
                == 1 + RecursiveCount(key, []);
                == 1 + 0;
                == 1;
                == RecursiveCount(key, []) + 1;
                == RecursiveCount(key, []) + county(elem, key);
            }
        } else {
            calc {
                RecursiveCount(key, [elem]);
                == RecursiveCount(key, [elem][..|[elem]|-1]);
                == RecursiveCount(key, []);
                == 0;
                == RecursiveCount(key, []) + 0;
                == RecursiveCount(key, []) + county(elem, key);
            }
        }
    } else {
        assert q + [elem] != [];
        assert |q + [elem]| == |q| + 1;
        assert (q + [elem])[|q + [elem]| - 1] == elem;
        
        if elem == key {
            calc {
                RecursiveCount(key, q + [elem]);
                == 1 + RecursiveCount(key, (q + [elem])[..|q + [elem]| - 1]);
                == { assert (q + [elem])[..|q + [elem]| - 1] == q; }
                   1 + RecursiveCount(key, q);
                == RecursiveCount(key, q) + 1;
                == RecursiveCount(key, q) + county(elem, key);
            }
        } else {
            calc {
                RecursiveCount(key, q + [elem]);
                == RecursiveCount(key, (q + [elem])[..|q + [elem]| - 1]);
                == { assert (q + [elem])[..|q + [elem]| - 1] == q; }
                   RecursiveCount(key, q);
                == RecursiveCount(key, q) + 0;
                == RecursiveCount(key, q) + county(elem, key);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method ProdAndCount(q: seq<int>, key: int) returns (prod: int, count: nat)
    ensures prod == RecursivePositiveProduct(q)
    ensures count == RecursiveCount(key, q)
// </vc-spec>
// <vc-code>
{
    prod := 1;
    count := 0;
    var i := 0;
    
    while i < |q|
        invariant 0 <= i <= |q|
        invariant prod == RecursivePositiveProduct(q[..i])
        invariant count == RecursiveCount(key, q[..i])
    {
        RecursivePositiveProductAppend(q[..i], q[i]);
        assert q[..i] + [q[i]] == q[..i+1];
        prod := prod * prody(q[i]);
        
        RecursiveCountAppend(key, q[..i], q[i]);
        count := count + county(q[i], key);
        
        i := i + 1;
    }
    
    assert q[..i] == q;
}
// </vc-code>

