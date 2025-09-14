// <vc-preamble>
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

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
    a.Length + 1 == c.Length
    && c[0] == 0
    && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}

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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added empty body to satisfy verifier */
lemma SumDecomposition(a: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  ensures sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j)
  decreases j - i
{
  if i < j {
    SumDecomposition(a, i, j - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): corrected loop-to range */
{
  if i == j {
    s := 0;
    return;
  }

  var c := new int[a.Length + 1];
  c[0] := 0;
  for k: int := 0 to a.Length
    invariant c.Length == a.Length + 1
    invariant 0 <= k <= a.Length
    invariant forall l: int :: 0 <= l <= k ==> c[l] == sum(a, 0, l)
  {
    c[k+1] := c[k] + a[k];
  }
  SumDecomposition(a, i, j);
  s := c[j] - c[i];
}
// </vc-code>
