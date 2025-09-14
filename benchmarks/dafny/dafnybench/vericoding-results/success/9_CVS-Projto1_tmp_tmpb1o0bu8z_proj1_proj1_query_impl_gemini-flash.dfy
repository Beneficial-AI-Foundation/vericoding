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
function suffix_sum (a:array<int>, i:int, j:int) :int
decreases j - i
reads a
requires 0 <= i <= j <= a.Length
{
    if i == j then
        0
    else
        a[i] + suffix_sum(a, i + 1, j)
}

lemma sum_is_suffix_sum(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, i, j) == suffix_sum(a, i, j)
  decreases j - i
{
  if i < j {
    calc {
      sum(a, i, j);
      a[j-1] + sum(a, i, j-1);
      { sum_is_suffix_sum(a, i, j - 1); }
      a[j-1] + suffix_sum(a, i, j-1);
      {
        // This is the crucial step now: prove that a[j-1] + suffix_sum(a, i, j-1)  == suffix_sum(a, i, j)
        // using the split lemma, we need to show suffix_sum(a, i, j) == suffix_sum(a, i, j-1) + suffix_sum(a, j-1, j)
        // and suffix_sum(a, j-1, j) == a[j-1] (which is true by definition of suffix_sum)
        suffix_sum_split(a, i, j-1, j);
      }
      suffix_sum(a, i, j);
    }
  }
}

lemma suffix_sum_split(a: array<int>, i: int, k: int, j: int)
  requires 0 <= i <= k <= j <= a.Length
  ensures suffix_sum(a, i, j) == suffix_sum(a, i, k) + suffix_sum(a, k, j)
  decreases k - i
{
  if i < k {
    calc {
      suffix_sum(a, i, j);
      a[i] + suffix_sum(a, i + 1, j);
      { suffix_sum_split(a, i + 1, k, j); }
      a[i] + (suffix_sum(a, i + 1, k) + suffix_sum(a, k, j));
      (a[i] + suffix_sum(a, i + 1, k)) + suffix_sum(a, k, j);
      suffix_sum(a, i, k) + suffix_sum(a, k, j);
    }
  } else if i == k {
    assert suffix_sum(a, i, j) == suffix_sum(a, i, k) + suffix_sum(a, k, j);
  }
}
// </vc-helpers>

// <vc-spec>
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  var current_sum := 0;
  var k := i;

  while k < j
    invariant i <= k <= j
    invariant current_sum == suffix_sum(a, i, k)
    decreases j - k
  {
    current_sum := current_sum + a[k];
    k := k + 1;
    suffix_sum_split(a, i, k-1, k);
    assert suffix_sum(a, i, k) == suffix_sum(a, i, k-1) + a[k-1];
  }
  s := current_sum;
  assert current_sum == suffix_sum(a, i, j);
  sum_is_suffix_sum(a, i, j);
}
// </vc-code>

