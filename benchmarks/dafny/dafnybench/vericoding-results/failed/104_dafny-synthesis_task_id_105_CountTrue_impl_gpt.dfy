function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}

// <vc-helpers>
lemma CountToStep(a: array<bool>, n: int)
  requires 0 <= n < a.Length
  ensures countTo(a, n+1) == countTo(a, n) + (if a[n] then 1 else 0)
{
  assert n + 1 > 0
  assert (n + 1) - 1 == n
  calc {
    countTo(a, n+1);
    == { }
    (if n+1 == 0 then 0 else countTo(a, (n+1)-1) + (if a[(n+1)-1] then 1 else 0));
    == { }
    countTo(a, n) + (if a[n] then 1 else 0);
  }
}
// </vc-helpers>

// <vc-spec>
method CountTrue(a: array<bool>) returns (result: int)
    requires a != null
    ensures result == countTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var acc := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant acc == countTo(a, i)
    decreases a.Length - i
  {
    var nextAcc := acc + (if a[i] then 1 else 0);
    calc {
      nextAcc;
      == { }
      acc + (if a[i] then 1 else 0);
      == { }
      countTo(a, i) + (if a[i] then 1 else 0);
      == { CountToStep(a, i); }
      countTo(a, i+1);
    }
    i := i + 1;
    acc := nextAcc;
  }
  result := acc;
}
// </vc-code>

