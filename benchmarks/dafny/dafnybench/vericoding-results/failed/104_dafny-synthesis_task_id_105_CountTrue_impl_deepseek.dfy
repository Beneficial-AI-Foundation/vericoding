function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}

// <vc-helpers>
lemma countToLemma(a: array<bool>, n: int, k: int)
  requires a != null
  requires 0 <= n && n <= a.Length
  requires 0 <= k && k <= a.Length - n
  ensures countTo(a, n + k) == countTo(a, n) + countTo(a[n..], k)
  decreases k
{
  if (k == 0) {
    // Base case
    assert a[n..] == [];
    assert countTo(a[n..], 0) == 0;
  } else {
    countToLemma(a, n, k-1);
    var m := n + k - 1;
    assert countTo(a, n + k) == countTo(a, n + k - 1) + (if a[n + k - 1] then 1 else 0);
    assert a[n..][k-1] == a[n + k - 1];
    assert countTo(a[n..], k) == countTo(a[n..], k-1) + (if a[n..][k-1] then 1 else 0);
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
  result := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == countTo(a, i)
  {
    if a[i] {
      result := result + 1;
    }
    i := i + 1;
  }
  if i == a.Length {
    countToLemma(a, 0, a.Length);
  }
}
// </vc-code>

