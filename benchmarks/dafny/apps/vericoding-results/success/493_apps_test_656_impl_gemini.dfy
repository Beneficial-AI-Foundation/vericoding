function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}

// <vc-helpers>
lemma {:induction} CountIsNonNegative(s: seq<int>)
  ensures count_negative_temp_days(s) >= 0
{
  if |s| > 0 {
    CountIsNonNegative(s[1..]);
  }
}

lemma {:induction} CountIsZeroIffAllNonNegative(s: seq<int>)
  ensures count_negative_temp_days(s) == 0 <==> (forall i :: 0 <= i < |s| ==> s[i] >= 0)
{
  if |s| > 0 {
    CountIsNonNegative(s[1..]);
    CountIsZeroIffAllNonNegative(s[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, temps: seq<int>) returns (result: int)
  requires n >= 1
  requires k >= 0 && k <= n
  requires |temps| == n
  requires forall i :: 0 <= i < n ==> -20 <= temps[i] <= 20
  ensures result == -1 <==> count_negative_temp_days(temps) > k
  ensures result != -1 ==> result >= 0
  ensures result == 0 ==> forall i :: 0 <= i < n ==> temps[i] >= 0
  ensures result > 0 ==> exists i :: 0 <= i < n && temps[i] < 0
// </vc-spec>
// <vc-code>
{
    var count := count_negative_temp_days(temps);
    CountIsNonNegative(temps);
    CountIsZeroIffAllNonNegative(temps);

    if count > k {
        result := -1;
    } else {
        result := count;
    }
}
// </vc-code>

