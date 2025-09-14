//Exercicio 1.a)
function sum (a:array<int>, i:int, j:int) :int
decreases j
reads a
requires 0 <= i <= j <= a.Length
{
    if i == j then
        0
    else
        a[j-1] + sum(a, i, j-1)
}

//Exercicio 1.b)

//Exercicio 1.c)

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
    a.Length + 1 == c.Length
    && c[0] == 0
    && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{
  assume{:axiom} false;
}

function mem<T(==)> (x: T, l:List<T>) : bool
decreases l
{
    match l
    case Nil => false
    case Cons(y,r)=> if (x==y) then true else mem(x,r)
}

// <vc-helpers>
function sum_to (a:array<int>, j:int) :int
decreases j
reads a
requires 0 <= j <= a.Length
{
    if j == 0 then
        0
    else
        a[j-1] + sum_to(a, j-1)
}

function sum_range (a:array<int>, i:int, j:int) :int
decreases j
reads a
requires 0 <= i <= j <= a.Length
{
    sum_to(a, j) - sum_to(a, i)
}

lemma sum_range_is_sum(a: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    ensures sum_range(a, i, j) == sum(a, i, j)
{
    if i == j {
        calc {
            sum_range(a,i,j);
            sum_to(a,j) - sum_to(a,i);
            { assert i == j; }
            sum_to(a,i) - sum_to(a,i);
            0;
            { assert i == j; }
            sum(a,i,j);
        }
    } else {
        calc {
            sum_range(a,i,j);
            sum_to(a,j) - sum_to(a,i);
            { reveal sum_to(); }
            (a[j-1] + sum_to(a,j-1)) - sum_to(a,i);
            a[j-1] + (sum_to(a,j-1) - sum_to(a,i));
            a[j-1] + sum_range(a,i,j-1);
            { 
                sum_range_is_sum(a,i,j-1);
            }
            a[j-1] + sum(a,i,j-1);
            { reveal sum(); }
            sum(a,i,j);
        }
    }
}

lemma sum_to_from_prefix(c: array<int>, a: array<int>, j: int)
    requires is_prefix_sum_for(a, c)
    requires 0 <= j <= a.Length
    ensures c[j] == sum_to(a, j)
{
    if j == 0 {
        calc {
            c[j];
            { assert is_prefix_sum_for(a, c); }
            c[0];
            { reveal is_prefix_sum_for(); }
            0;
            sum_to(a, 0);
        }
    } else {
        calc {
            c[j];
            { assert is_prefix_sum_for(a, c); }
            sum(a, 0, j);
            { 
                reveal sum();
                assert a[j-1] + sum(a,0,j-1) == sum(a,0,j);
            }
            a[j-1] + sum(a,0,j-1);
            {
                sum_to_from_prefix(c, a, j-1);
                assert c[j-1] == sum_to(a, j-1);
                calc {
                    sum(a,0,j-1);
                    { sum_range_is_sum(a,0,j-1); }
                    sum_range(a,0,j-1);
                    sum_to(a,j-1) - sum_to(a,0);
                    sum_to(a,j-1) - 0;
                    sum_to(a,j-1);
                }
            }
            a[j-1] + sum_to(a, j-1);
            sum_to(a, j);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
// </vc-spec>
// <vc-code>
{
    sum_range_is_sum(a, i, j);
    sum_to_from_prefix(c, a, j);
    assert c[j] == sum_to(a, j);
    sum_to_from_prefix(c, a, i);
    assert c[i] == sum_to(a, i);
    r := c[j] - c[i];
}
// </vc-code>

