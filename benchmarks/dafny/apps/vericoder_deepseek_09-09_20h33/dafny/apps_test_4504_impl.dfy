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
    if i % 2 == 0 && i <= k {
      var half_k := k / 2;
      var half_i := i / 2;
      
      // Prove that s[..i] is an even string
      assert s[..half_i] == s[half_k..half_k + half_i] by {
        assert s[..half_k] == s[half_k..k];
      };
      assert s[half_i..2*half_i] == s[half_k + half_i..half_k + 2*half_i] by {
        assert s[..half_k] == s[half_k..k];
      };
      assert s[..half_i] == s[half_i..i];
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
    invariant exists k :: result <= k <= n && k % 2 == 0 && IsEvenString(S[..k])
    decreases result
  {
    var current_result := result;
    if IsEvenString(S[..current_result]) {
      // Check if this is the maximal solution
      var temp := current_result + 2;
      var found_larger := false;
      
      while temp <= n
        invariant current_result < temp <= n + 2
        invariant temp % 2 == 0
        invariant !IsEvenString(S[..current_result + 2]) || found_larger
        decreases n - temp
      {
        if IsEvenString(S[..temp]) {
          found_larger := true;
          break;
        }
        temp := temp + 2;
      }
      
      if !found_larger {
        // This is the maximal solution
        result := current_result;
        return;
      }
    }
    result := result - 2;
  }
  // Minimal case when loop ends
  result := 2;
  assert IsEvenString(S[..2]) ==> S[0] == S[1];
}
// </vc-code>

