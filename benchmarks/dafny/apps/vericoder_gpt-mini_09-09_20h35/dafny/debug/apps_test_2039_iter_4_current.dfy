predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n
}

function CountLocalExtrema(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    |set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))|
}

predicate IsLocalExtremum(a: seq<int>, i: int)
    requires 0 <= i < |a|
{
    1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}

// <vc-helpers>
lemma CountLocalExtrema_eq_set(n: int, a: seq<int>, s: set<int>)
    requires ValidInput(n, a)
    requires forall j :: j in s <==> 1 <= j < n - 1 && IsLocalExtremum(a, j)
    ensures CountLocalExtrema(n, a) == |s|
{
    // Unfold the definition of CountLocalExtrema
    assert CountLocalExtrema(n, a) == |set i | 1 <= i < n - 1 && IsLocalExtremum(a, i)|;
    // The membership condition in the requires already gives extensionality
    assert forall j :: j in s <==> j in (set i | 1 <= i < n - 1 && IsLocalExtremum(a, i));
    // Hence the cardinalities are equal
    assert |s| == |set i | 1 <= i < n - 1 && IsLocalExtremum(a, i)|;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures n <= 2 ==> result == 0
    ensures n > 2 ==> result <= n - 2
    ensures result == CountLocalExtrema(n, a)
// </vc-spec>
// <vc-code>
{
  if n <= 2 {
    result := 0;
    return;
  }
  result := 0;
  ghost var s: set<int> := {};
  var k := 1;
  while k < n - 1
    invariant 1 <= k <= n - 1
    invariant result == |s|
    invariant forall j :: j in s <==> 1 <= j < k && IsLocalExtremum(a, j)
    invariant result <= k - 1
    decreases n - k
  {
    if IsLocalExtremum(a, k) {
      result := result + 1;
      s := s + {k};
    }
    k := k + 1;
  }
  // At loop exit k == n - 1
  assert k == n - 1;
  // Relate the collected set s to the CountLocalExtrema function
  CountLocalExtrema_eq_set(n, a, s);
  // From invariants we have result == |s| and by the lemma |s| == CountLocalExtrema(n,a)
  // so the postcondition result == CountLocalExtrema(n,a) holds
}
// </vc-code>

