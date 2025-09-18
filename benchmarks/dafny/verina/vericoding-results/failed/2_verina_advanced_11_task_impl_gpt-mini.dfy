// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): ZeroOccurrencesForAbsent - proves CountOccurrences is 0 when no element equals x */
lemma ZeroOccurrencesForAbsent(x: int, lst: seq<int>)
  ensures (forall i :: 0 <= i < |lst| ==> lst[i] != x) ==> CountOccurrences(x, lst) == 0
{
  if forall i :: 0 <= i < |lst| ==> lst[i] != x {
    var A := set i | 0 <= i < |lst| && lst[i] == x;
    assert CountOccurrences(x, lst) == |A|;
    assert A == {};
    assert |A| == 0;
    assert CountOccurrences(x, lst) == 0;
  }
}

/* helper modified by LLM (iteration 5): TwoMajoritiesEqual - two different values cannot both be majority */
lemma TwoMajoritiesEqual(s: seq<int>, a: int, b: int)
  requires CountOccurrences(a, s) > |s|/2 && CountOccurrences(b, s) > |s|/2
  ensures a == b
{
  var n := |s|;
  if a != b {
    var A := set i | 0 <= i < n && s[i] == a;
    var B := set i | 0 <= i < n && s[i] == b;
    // prove A and B are disjoint
    assert forall k :: k in A ==> k !in B {
      if k in A && k in B {
        assert s[k] == a;
        assert s[k] == b;
        assert a == b;
      }
    }
    assert A * B == {};
    // union is subset of indices 0..n-1
    assert forall k :: k in A + B ==> 0 <= k < n {
      if k in A + B {
        if k in A { assert 0 <= k < n; } else { assert 0 <= k < n; }
      }
    }
    assert |A + B| <= n;
    assert CountOccurrences(a, s) == |A|;
    assert CountOccurrences(b, s) == |B|;
    assert |A + B| == |A| + |B|;
    assert CountOccurrences(a, s) + CountOccurrences(b, s) == |A + B|;
    assert CountOccurrences(a, s) + CountOccurrences(b, s) > n;
    assert CountOccurrences(a, s) + CountOccurrences(b, s) <= n;
    assert false;
  }
}

// </vc-helpers>

// <vc-spec>
method FindMajorityElement(lst: array<int>) returns (result: int)
    ensures var lst_seq := lst[..];
            var n := |lst_seq|;
            var majority := CountOccurrences(result, lst_seq) > n / 2 && 
                          forall x :: CountOccurrences(x, lst_seq) <= n / 2 || x == result;
            (result == -1 ==> forall x :: CountOccurrences(x, lst_seq) <= n / 2) &&
            (result != -1 ==> majority)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): naive majority check counting each distinct element with precise invariants relating occ to CountOccurrences */
  var n := |lst[..]|;
  result := -1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant (result == -1) ==> (forall k :: 0 <= k < i ==> CountOccurrences(lst[k], lst[..]) <= n/2)
    decreases n - i
  {
    var x := lst[i];
    var occ := 0;
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant 0 <= occ <= j
      invariant occ == |set k | 0 <= k < j && lst[k] == x|
      decreases n - j
    {
      if lst[j] == x { occ := occ + 1; }
      j := j + 1;
    }
    assert occ == |set k | 0 <= k < n && lst[k] == x|;
    assert occ == CountOccurrences(x, lst[..]);
    if occ * 2 > n {
      result := x;
      return;
    }
    i := i + 1;
  }
}

// </vc-code>
