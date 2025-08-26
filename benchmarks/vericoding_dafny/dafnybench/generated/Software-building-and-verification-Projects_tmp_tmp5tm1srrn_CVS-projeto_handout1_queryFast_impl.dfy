// 1 a)

// [ai, aj[
// <vc-spec>
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
  decreases j
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}

// 1 b)

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]

// <vc-helpers>
lemma sum_diff_lemma(a: array<int>, c: array<int>, i: int, j: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a, c)
  ensures sum(a, i, j) == c[j] - c[i]
{
  if i == j {
    // Base case: sum(a, i, i) == 0 and c[i] - c[i] == 0
  } else {
    // Inductive case: use the recursive structure of sum
    sum_diff_lemma(a, c, i, j-1);
    // Now we know sum(a, i, j-1) == c[j-1] - c[i]
    // And sum(a, i, j) == a[j-1] + sum(a, i, j-1)
    // From is_prefix_sum_for, we know c[j] == sum(a, 0, j) and c[j-1] == sum(a, 0, j-1)
    // So c[j] - c[j-1] == sum(a, 0, j) - sum(a, 0, j-1) == a[j-1]
    proof(a, 0, j, j-1);
  }
}
// </vc-helpers>

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c)
  ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
  sum_diff_lemma(a, c, i, j);
  r := c[j] - c[i];
}
// </vc-code>

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{
  a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}

lemma proof(a: array<int>, i: int, j: int, k:int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
  decreases j - k
{
  if k == j {
    // Base case: sum(a, k, j) == sum(a, j, j) == 0
    // So sum(a, i, k) + sum(a, k, j) == sum(a, i, k) + 0 == sum(a, i, k) == sum(a, i, j)
  } else {
    // Inductive case
    proof(a, i, j, k+1);
    // We know sum(a, i, k+1) + sum(a, k+1, j) == sum(a, i, j)
    // And sum(a, k, k+1) == a[k]
    // We need to show sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
    // sum(a, k, j) == a[j-1] + sum(a, k, j-1) by definition
    // We can use the recursive structure to prove this
  }
}


// 2

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
  l := Nil;
  var i := a.Length - 1;
  while i >= 0
    invariant 0 <= i+1 <= a.Length
    invariant forall j: int :: i < j < a.Length ==> mem(a[j], l)
    invariant forall x: T :: mem(x, l) ==> exists y: int :: i+1 <= y < a.Length && a[y] == x
    decreases i
  {
    l := Cons(a[i], l);
    i := i - 1;
  }
}

function mem<T(==)> (x: T, l: List<T>) : bool
{
  match l
  case Nil => false
  case Cons(h, t) => h == x || mem(x, t)
}