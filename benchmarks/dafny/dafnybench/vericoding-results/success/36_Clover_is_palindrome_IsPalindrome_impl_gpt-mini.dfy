

// <vc-helpers>
lemma mirror_index(n: nat, k: nat)
  requires k < n
  requires k >= n/2
  ensures n - k - 1 < n/2 || n - k - 1 == k
{
  var j := n - k - 1;
  if 2*(n/2) == n {
    // n even: n = 2*(n/2)
    assert j <= n - (n/2) - 1;
    assert n - (n/2) - 1 == n/2 - 1;
    assert n/2 - 1 < n/2;
    assert j < n/2;
  } else {
    // n odd: n = 2*(n/2) + 1
    assert n == 2*(n/2) + 1;
    assert j <= n - (n/2) - 1;
    assert n - (n/2) - 1 == n/2;
    if j < n/2 {
      // done
    } else {
      // j >= n/2 and j <= n/2 => j == n/2, and then k == n/2, so j == k
      assert j == n/2;
      assert k == n - j - 1;
      assert k == n/2;
      assert j == k;
    }
  }
}

lemma PalindromeHalfImpliesFull(x: seq<char>, n: nat)
  requires n == |x|
  requires forall j :: 0 <= j < n/2 ==> x[j] == x[n - j - 1]
  ensures forall k :: 0 <= k < n ==> x[k] == x[n - k - 1]
{
  forall k | 0 <= k < n
    ensures x[k] == x[n - k - 1]
  {
    if k < n/2 {
      // directly from the hypothesis
      assert x[k] == x[n - k - 1];
    } else {
      var j := n - k - 1;
      mirror_index(n, k);
      if j < n/2 {
        // use the hypothesis on j
        assert x[j] == x[n - j - 1];
        // n - j - 1 == k, so conclude
        assert n - j - 1 == k;
        assert x[k] == x[n - k - 1];
      } else {
        // then j == k, so equality is trivial
        assert j == k;
        assert x[k] == x[n - k - 1];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
// </vc-spec>
// <vc-code>
{
  result := forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1];
  return;
}
// </vc-code>

