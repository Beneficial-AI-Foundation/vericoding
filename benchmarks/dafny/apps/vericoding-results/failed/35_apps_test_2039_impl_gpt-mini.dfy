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
    // From ValidInput we know the length agreement
    assert n == |a|;

    // Prove extensional equality between s and the set used in CountLocalExtrema
    assert forall j :: (j in s) <==> (j in (set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))));
    {
        fix j;
        if j in s {
            // From the requires quantifier we get the predicate form
            assert 1 <= j < n - 1 && IsLocalExtremum(a, j);
            // From IsLocalExtremum we can obtain the comparison property
            assert (a[j] > a[j-1] && a[j] > a[j+1]) || (a[j] < a[j-1] && a[j] < a[j+1]);
            assert j in (set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1])));
        } else {
            // From the requires quantifier we know the negation of the RHS
            assert !(1 <= j < n - 1 && IsLocalExtremum(a, j));
            if 1 <= j < n - 1 {
                // If the index range holds, then !IsLocalExtremum implies the comparison fails
                assert !IsLocalExtremum(a, j);
                assert !((a[j] > a[j-1] && a[j] > a[j+1]) || (a[j] < a[j-1] && a[j] < a[j+1]));
            }
            assert !(j in (set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))));
        }
    }

    // From extensional equality we get equal cardinalities
    assert |s| == |set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))|;
    // By definition of CountLocalExtrema
    assert CountLocalExtrema(n, a) == |set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))|;
    assert CountLocalExtrema(n, a) == |s|;
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
    k := k +
// </vc-code>

