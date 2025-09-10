predicate IsEvenString(s: string)
{
    |s| >= 2 && |s| % 2 == 0 && s[..|s|/2] == s[|s|/2..]
}

predicate ValidInput(S: string)
{
    |S| >= 2 && IsEvenString(S)
}

predicate ValidSolution(S: string, result: int)
{
    2 <= result < |S| && result % 2 == 0 && IsEvenString(S[..result])
}

predicate IsMaximalSolution(S: string, result: int)
{
    ValidSolution(S, result) && 
    forall k :: result < k < |S| && k % 2 == 0 ==> !IsEvenString(S[..k])
}

// <vc-helpers>
lemma EvenPrefixLemma(s: string, k: int)
  requires |s| >= 2 && k % 2 == 0 && 2 <= k <= |s|
  requires IsEvenString(s[..k])
  ensures forall i :: 2 <= i <= k && i % 2 == 0 ==> IsEvenString(s[..i])
{
  var i := 2;
  while i <= k
    invariant 2 <= i <= k + 1
    invariant forall j :: 2 <= j < i && j % 2 == 0 ==> IsEvenString(s[..j])
  {
    if i % 2 == 0 {
      assert IsEvenString(s[..k]);
      var half := k / 2;
      assert s[..half] == s[half..k];
      
      if i <= k {
        var half_i := i / 2;
        var prefix := s[..i];
        var left_half := prefix[..half_i];
        var right_half := prefix[half_i..];
        assert left_half == s[..half_i];
        assert right_half == s[half_i..i];
        assert s[..half_i] == s[half_i..2*half_i];
        assert 2*half_i == i;
      }
    }
    i := i + 2;
  }
}

lemma MaximalSolutionLemma(S: string, result: int)
  requires ValidSolution(S, result)
  requires forall k :: result < k < |S| && k % 2 == 0 ==> !IsEvenString(S[..k])
  ensures IsMaximalSolution(S, result)
{
}
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    requires exists k :: ValidSolution(S, k)
    ensures ValidSolution(S, result)
    ensures IsMaximalSolution(S, result)
// </vc-spec>
// <vc-code>
{
  var n := |S|;
  result := n;
  if result % 2 != 0 {
    result := result - 1;
  }
  
  while result >= 2
    invariant 0 <= result <= n
    invariant result % 2 == 0
    invariant exists k :: 2 <= k <= n && k % 2 == 0 && IsEvenString(S[..k])
    decreases result
  {
    if IsEvenString(S[..result]) {
      // Prove maximality
      var temp := result;
      while temp < n
        invariant result <= temp <= n
        invariant temp % 2 == 0
        invariant IsEvenString(S[..result])
        decreases n - temp
      {
        temp := temp + 2;
        if temp <= n {
          assert !IsEvenString(S[..temp]);
        }
      }
      return;
    }
    result := result - 2;
  }
  result := 2;
  assert IsEvenString(S[..2]) ==> S[0] == S[1];
}
// </vc-code>

