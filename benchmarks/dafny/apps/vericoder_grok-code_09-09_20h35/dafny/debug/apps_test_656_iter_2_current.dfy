function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}

// <vc-helpers>
lemma CountZeroIffNoNegative(temps: seq<int>)
  ensures count_negative_temp_days(temps) == 0 <==> forall i :: 0 <= i < |temps| ==> temps[i] >= 0
{
  if |temps| == 0 {
    // Base case: true <==> true
  } else {
    // Induction on tail
    CountZeroIffNoNegative(temps[1..]);
    // count(temps) == 0 iff (if temps[0] < 0 then 1 else 0) == 0 and count(temps[1..]) == 0
    // iff temps[0] >= 0 and forall in tail
  }
}

lemma CountPositiveIffExistsNegative(temps: seq<int>)
  ensures count_negative_temp_days(temps) > 0 <==> exists i :: 0 <= i < |temps| && temps[i] < 0
{
  if |temps| == 0 {
    // Base case: false <==> false
  } else {
    // Induction on tail
    CountPositiveIffExistsNegative(temps[1..]);
    // count(temps) > 0 iff (temps[0] < 0) or count(temps[1..]) > 0
    // iff (exists 0) or exists in tail
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
  var cnt := count_negative_temp_days(temps);
  if cnt > k {
    result := -1;
  } else if cnt == 0 {
    CountZeroIffNoNegative(temps);
    result := 0;
  } else {
    CountPositiveIffExistsNegative(temps);
    result := 1;
  }
}
// </vc-code>

