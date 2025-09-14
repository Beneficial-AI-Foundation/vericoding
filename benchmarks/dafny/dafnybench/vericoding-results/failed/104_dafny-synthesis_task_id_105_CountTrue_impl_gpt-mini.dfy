function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}

// <vc-helpers>
lemma CountTo_Succ(a: array<bool>, i: int)
  requires a != null
  requires 0 <= i && i < a.Length
  reads a
  ensures countTo(a, i+1) == countTo(a, i) + (if a[i] then 1 else 0)
{
  // Unfold the definition of countTo at n = i+1
  assert countTo(a, i+1) == (if i+1 == 0 then 0 else countTo(a, i) + (if a[i] then 1 else 0));
  // From the precondition 0 <= i we have i+1 != 0, so the else-branch holds
  assert i + 1 != 0;
  assert countTo(a, i+1) == countTo(a, i) + (if a[i] then 1 else 0);
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
  var cnt := 0;
  while i < a.Length
    invariant 0 <= i && i <= a.Length
    invariant cnt == countTo(a, i)
  {
    cnt := cnt + (if a[i] then 1 else 0);
    CountTo_Succ(a, i);
    i := i + 1;
  }
  result := cnt;
}
// </vc-code>

